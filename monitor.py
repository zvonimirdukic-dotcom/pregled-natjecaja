"""Pregled javne nabave s izričitim označavanjem nepotpunih izvora."""
from __future__ import annotations

import argparse
import hashlib
import html
import io
import json
import os
import re
import smtplib
import time
import unicodedata
import zipfile
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import urljoin, urlparse, urldefrag, urlencode, unquote
from zoneinfo import ZoneInfo

import requests
import yaml
from bs4 import BeautifulSoup

TZ = ZoneInfo("Europe/Zagreb")
ROOT = Path(__file__).resolve().parent


def norm(s):
    return "".join(
        c for c in unicodedata.normalize("NFKD", s.lower())
        if not unicodedata.combining(c)
    )


PRODUCT = re.compile(
    r"uredsk.{0,25}(?:materijal|potrep|potreb|pribor|papir)|"
    r"kancelarij|toner|tint[aeu]|pisac|printer|fotokop|kopirn|"
    r"ciscenj|higijen|dezinf|toalet|wc[- ]*papir|papirn|"
    r"ubrusi?|rucnici?|sapun|deterdzent|sredstv.{0,20}pranj|"
    r"sanitarni potrosni|potrosni materijal"
)
CPV = re.compile(
    r"\b(?:3019\d{4}|30125\d{3}|398\d{5}|337\d{5}|"
    r"228\d{5}|229\d{5}|30237\d{3})\b"
)
PROC = re.compile(r"nabav|ponud|nadmetanj|troskovnik|natjecaj|poziv")
EXCLUDE = re.compile(r"zaposljav|radni odnos|radno mjesto|zakup|stipendij")
REGION = re.compile(
    r"slavonski brod|nova gradiska|pozeg|brodsko.posav|hr023|hr024"
)
DATE_RE = re.compile(
    r"\b(\d{1,2})\s*[./-]\s*(\d{1,2})\s*[./-]\s*(20\d{2})\b"
)


def parse_date(s):
    s = norm(s or "")
    months = {
        "sijecnja": 1,
        "veljace": 2,
        "ozujka": 3,
        "travnja": 4,
        "svibnja": 5,
        "lipnja": 6,
        "srpnja": 7,
        "kolovoza": 8,
        "rujna": 9,
        "listopada": 10,
        "studenoga": 11,
        "studenog": 11,
        "prosinca": 12,
    }
    m = DATE_RE.search(s)
    if m:
        parts = (int(m[3]), int(m[2]), int(m[1]))
    else:
        m = re.search(
            r"\b(20\d{2})-(\d{2})-(\d{2})(?=t|\b)", s
        )
        if m:
            parts = tuple(map(int, m.groups()))
        else:
            m = re.search(
                r"\b(\d{1,2})\.?\s+(" + "|".join(months)
                + r")\s+(20\d{2})\b", s
            )
            if not m:
                return ""
            parts = (int(m[3]), months[m[2]], int(m[1]))
    try:
        return date(*parts).isoformat()
    except ValueError:
        return ""


def publication_date(soup, text):
    if soup is not None:
        for node in soup.select(
            'meta[property="article:published_time"], '
            'meta[itemprop="datePublished"]'
        ):
            value = parse_date(node.get("content", ""))
            if value:
                return value

        scope = soup.find("article") or soup.find("main") or soup
        for node in scope.select(
            '[itemprop="datePublished"], time.published, .published time'
        ):
            value = parse_date(
                node.get("datetime") or node.get("content")
                or node.get_text(" ", strip=True)
            )
            if value:
                return value

    match = re.search(
        r"(?:objavljeno|datum objave|dodano datuma)\s*:?\s*"
        r"(\d{1,2}\s*[./-]\s*\d{1,2}\s*[./-]\s*20\d{2}"
        r"|20\d{2}-\d{2}-\d{2}"
        r"|\d{1,2}\.?\s+[a-z]+\s+20\d{2})",
        norm(text),
    )
    return parse_date(match[1]) if match else ""


def relevant(s):
    return bool(PRODUCT.search(norm(s)) or CPV.search(s))


def signature(item):
    data = json.dumps(
        item, ensure_ascii=False, sort_keys=True
    ).encode()
    return hashlib.sha256(data).hexdigest()


def source_status(source, status, count=0, detail=""):
    return dict(
        source=source, status=status, count=count, detail=detail
    )


def parse_eojn_row(headers, cells, links, source):
    if len(headers) != len(cells):
        raise ValueError("Promijenjena struktura EOJN tablice")

    d = dict(zip(headers, cells))
    title = d.get("Naziv postupka", "")
    buyer = d.get("Naručitelj", "")
    url = next((u for u in links if "/tender-eo/" in u), "")

    if not title or not buyer or not url:
        raise ValueError(
            "EOJN redak nema predmet, naručitelja ili trajni link"
        )

    return dict(
        source=source,
        buyer=buyer,
        title=title,
        url=url,
        published=parse_date(d.get("Datum objave", "")),
        deadline=d.get("Rok za dostavu", ""),
        value=d.get("Proc. vrijednost", ""),
        cpv=d.get("CPV", ""),
        reference=d.get("Evid. broj", d.get("Broj", "")),
        kind=d.get("Naziv objave", d.get("Vrsta postupka", "")),
        status=d.get("Status", ""),
        region=d.get("NUTS", ""),
        evidence="Javna EOJN tablica",
    )


def _collect_eojn_once(since, max_pages=400, only_sources=None):
    from playwright.sync_api import sync_playwright

    results, coverage = [], []
    feeds = [
        (
            "Postupci (javna i jednostavna nabava)",
            "procurements-all",
            "NoticePublishDate",
        ),
        (
            "Objave i izmjene",
            "notices-all",
            "PublishDate",
        ),
    ]

    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        context = browser.new_context(
            locale="hr-HR", timezone_id="Europe/Zagreb"
        )
        page = context.new_page()
        page.set_default_timeout(60000)

        for label, path, field in feeds:
            name = "EOJN — " + label
            if only_sources is not None and name not in only_sources:
                continue

            rows_read, expected, visited = 0, None, set()

            try:
                query = urlencode({
                    "initFilter": json.dumps(
                        [field, ">=", since], separators=(",", ":")
                    )
                })
                page.goto(
                    "https://eojn.hr/" + path + "?" + query,
                    wait_until="domcontentloaded",
                )

                cookie = page.get_by_role(
                    "button", name="Slažem se", exact=True
                )
                if cookie.count() and cookie.is_visible():
                    cookie.click()

                page.locator('[role="columnheader"]').first.wait_for()
                page.wait_for_function("""
                    () => document.querySelector('tr.dx-data-row')
                    || [...document.querySelectorAll('.dx-datagrid-nodata')]
                       .some(e => e.offsetParent !== null)
                """)

                headers = [
                    h.strip()
                    for h in page.locator(
                        '[role="columnheader"]'
                    ).all_text_contents()
                ]

                for page_no in range(max_pages):
                    nav = page.get_by_role(
                        "navigation", name="Navigacija stranicama"
                    ).inner_text()

                    match = re.search(
                        r"Stranica\s+(\d+)\s+od\s+(\d+)"
                        r"\s+\(([\d., ]+)\s+stav",
                        nav,
                    )
                    if not match:
                        raise ValueError(
                            "Nije potvrđen broj stranica EOJN-a"
                        )

                    current = int(match[1])
                    total = int(match[2])
                    count = int(re.sub(r"\D", "", match[3]))

                    if expected is None:
                        expected = count
                    elif expected != count:
                        raise ValueError(
                            "Broj objava promijenio se tijekom pregleda; "
                            "ponoviti pregled"
                        )

                    rendered = page.locator(
                        "tr.dx-data-row"
                    ).evaluate_all("""
                        els => els.map(e => ({
                            cells: [...e.querySelectorAll('[role=gridcell]')]
                                   .map(c => c.textContent.trim()),
                            links: [...e.querySelectorAll('a[href]')]
                                   .map(a => a.href)
                        }))
                    """)

                    fingerprint = signature(rendered)
                    if fingerprint in visited and count:
                        raise ValueError(
                            "Ponavlja se ista stranica rezultata"
                        )
                    visited.add(fingerprint)

                    for raw in rendered:
                        item = parse_eojn_row(
                            headers, raw["cells"], raw["links"], name
                        )
                        if (
                            not item["published"]
                            or item["published"] < since
                        ):
                            raise ValueError(
                                "Datum EOJN retka ne odgovara "
                                "traženom razdoblju"
                            )

                        rows_read += 1
                        if relevant(item["title"] + " " + item["cpv"]):
                            results.append(item)

                    if current >= total:
                        if rows_read != expected:
                            raise ValueError(
                                f"Pročitano {rows_read} od {expected} stavki"
                            )
                        break

                    old_rows = page.locator(
                        "tr.dx-data-row"
                    ).all_text_contents()

                    page.get_by_role(
                        "button", name="Slijedeća stranica", exact=True
                    ).click()

                    page.wait_for_function("""
                        old => document.querySelector(
                            '[aria-label="Navigacija stranicama"]'
                        )?.innerText !== old
                    """, arg=nav)

                    page.wait_for_function("""
                        old => JSON.stringify(
                            [...document.querySelectorAll('tr.dx-data-row')]
                            .map(e => e.textContent)
                        ) !== JSON.stringify(old)
                    """, arg=old_rows)

                    page.wait_for_function("""
                        () => ![...document.querySelectorAll('.dx-loadpanel')]
                              .some(e => e.offsetParent !== null)
                    """)
                else:
                    raise ValueError(
                        f"Dosegnut limit {max_pages} stranica"
                    )

                coverage.append(source_status(
                    name,
                    "PREGLEDANO",
                    rows_read,
                    f"Razdoblje od {since}; svi retci filtriranog popisa",
                ))

            except Exception as e:
                coverage.append(source_status(
                    name,
                    "NEPOTPUNO",
                    rows_read,
                    str(e).splitlines()[0][:220],
                ))

        context.close()
        browser.close()

    return results, coverage


def collect_eojn(since, max_pages=400):
    items, coverage = _collect_eojn_once(since, max_pages)
    failed = {
        c["source"] for c in coverage
        if c["status"] != "PREGLEDANO"
    }
    if not failed:
        return items, coverage

    print("EOJN: ponavljam nepotpune popise.", flush=True)

    try:
        retry_items, retry_coverage = _collect_eojn_once(
            since, max_pages, only_sources=failed
        )
    except Exception as exc:
        for c in coverage:
            if c["source"] in failed:
                c["detail"] += (
                    " | Ponovni pokušaj nije uspio: "
                    + type(exc).__name__
                )
        return items, coverage

    recovered = {
        c["source"] for c in retry_coverage
        if c["status"] == "PREGLEDANO"
    }

    merged = {}
    for item in (
        [i for i in items if i["source"] not in recovered]
        + retry_items
    ):
        key = (
            item["source"],
            item["url"],
            item["reference"],
            item["kind"],
        )
        merged[key] = item

    retry_status = {
        c["source"]: c for c in retry_coverage
    }
    for index, old in enumerate(coverage):
        if old["source"] in retry_status:
            new = dict(retry_status[old["source"]])
            new["detail"] += " | Izvršen ponovni pokušaj."
            coverage[index] = new

    return list(merged.values()), coverage


def fetch_document(session, url):
    with session.get(url, timeout=(12, 25), stream=True) as r:
        r.raise_for_status()
        parts, size = [], 0

        for part in r.iter_content(65536):
            size += len(part)
            if size > 12_000_000:
                raise ValueError("Dokument veći od 12 MB")
            parts.append(part)

        content = b"".join(parts)
        mime = r.headers.get("Content-Type", "").lower()
        final = r.url

        if "pdf" in mime or content.startswith(b"%PDF"):
            from pypdf import PdfReader

            reader = PdfReader(io.BytesIO(content))
            if len(reader.pages) > 100:
                raise ValueError("PDF veći od 100 stranica")

            text = "\n".join(
                p.extract_text() or "" for p in reader.pages
            )
            if len(text.strip()) < 50:
                raise ValueError(
                    "PDF bez čitljivog teksta; potreban OCR"
                )
            return final, text, None

        if urlparse(final).path.lower().endswith(".docx"):
            with zipfile.ZipFile(io.BytesIO(content)) as z:
                info = z.getinfo("word/document.xml")
                if info.file_size > 12_000_000:
                    raise ValueError("Prevelik DOCX XML")
                text = BeautifulSoup(
                    z.read(info), "xml"
                ).get_text(" ", strip=True)
            return final, text, None

        if urlparse(final).path.lower().endswith(
            (".doc", ".xls", ".xlsx", ".zip")
        ):
            raise ValueError(
                "Privitak zahtijeva dodatni čitač; provjeriti izvor"
            )

        if (
            "html" not in mime
            and not content.lstrip().lower().startswith(
                (b"<!doctype html", b"<html")
            )
        ):
            raise ValueError("Nepodržan format dokumenta")

        soup = BeautifulSoup(content, "html.parser")
        for e in soup.select("script,style,nav,header,footer"):
            e.decompose()

        main = (
            soup.find("main") or soup.find("article")
            or soup.body or soup
        )
        return final, main.get_text(" ", strip=True), soup


def candidate_links(soup, base, procurement_page):
    found = {}

    base_tag = soup.find("base", href=True)
    if base_tag:
        base = urljoin(base, html.unescape(base_tag["href"]))

    for a in soup.find_all("a", href=True):
        raw = html.unescape(a["href"]).strip()
        if raw.lower().startswith(
            ("#", "javascript:", "mailto:", "tel:")
        ):
            continue

        url = urldefrag(urljoin(base, raw))[0]
        if urlparse(url).scheme not in ("https", "http"):
            continue

        title = a.get_text(" ", strip=True) or a.get("title", "")
        slug = unquote(
            urlparse(url).path.rstrip("/").rsplit("/", 1)[-1]
        )
        combined = re.sub(
            r"[-_]+", " ", norm(title + " " + slug)
        )

        if EXCLUDE.search(combined) or re.search(
            r"pravilnik|sprjecavanje sukoba|registar ugovor|plan nabav|"
            r"radn(?:og|i|o) odnos|radn(?:og|o|a) mjest|prijam u sluzbu|"
            r"prijem u radni|zasnivanje radnog|sklapanje radnog",
            combined,
        ):
            continue

        if re.search(
            r"\.(?:jpe?g|png|gif|svg|webp|mp4|mp3|css|js)$",
            urlparse(url).path,
            re.I,
        ):
            continue

        parent = a.find_parent(["tr", "article", "li", "p"])
        context = (
            parent.get_text(" ", strip=True)[:1500]
            if parent else title
        )
        file = bool(
            re.search(r"\.(pdf|docx?|xlsx?)(?:$|[?])", url, re.I)
        )
        pagination = bool(
            re.search(r"(/page/\d|[?&](page|start|paged)=)", url)
            or norm(title) in (
                "sljedeca",
                "sljedeca stranica",
                "starije objave",
                "next",
            )
        )

        if (
            PROC.search(combined)
            or relevant(title)
            or (procurement_page and (file or pagination))
        ):
            found[url] = dict(
                title=title, context=context, file=file
            )

    return found


def scan_site(source, today, max_pages=60):
    name, start = source["name"], source["url"]
    queue = [(start, "", "")]
    seen, found, errors = set(), {}, []
    deadline = time.monotonic() + 150
    domain = urlparse(start).netloc.lower().removeprefix("www.")

    with requests.Session() as session:
        session.headers["User-Agent"] = (
            "GeneralTradeProcurementMonitor/2.0 (public procurement)"
        )

        while (
            queue
            and len(seen) < max_pages
            and time.monotonic() < deadline
        ):
            url, anchor, parent_context = queue.pop(0)
            if url in seen:
                continue
            seen.add(url)

            try:
                final, text, soup = fetch_document(session, url)

                if url == start:
                    domain = (
                        urlparse(final).netloc.lower()
                        .removeprefix("www.")
                    )

                title = anchor
                if soup:
                    heading = soup.find("h1")
                    if heading:
                        title = heading.get_text(" ", strip=True)

                    if not title or norm(title) in (
                        "procitajte vise",
                        "saznajte vise",
                        "vise",
                        "detalji",
                    ):
                        title = unquote(
                            urlparse(final).path.rstrip("/")
                            .rsplit("/", 1)[-1]
                        ).replace("-", " ")

                title = (title or source["name"])[:350]
                procurement = bool(
                    PROC.search(norm(title + " " + url))
                )
                date_value = publication_date(soup, text)

                if (
                    (relevant(title) or (soup is None and relevant(text)))
                    and (procurement or PROC.search(norm(parent_context)))
                    and not EXCLUDE.search(norm(title))
                    and not re.search(
                        r"pravilnik|plan nabave|registar ugovor",
                        norm(title),
                    )
                ):
                    generic = norm(title).strip() in (
                        "javna nabava",
                        "jednostavna nabava",
                        "nabava",
                        "natjecaji",
                        "novosti",
                        "postupci javne nabave",
                    )
                    recent = (
                        not date_value
                        or date_value >= (
                            today - timedelta(days=30)
                        ).isoformat()
                    )

                    if url != start and not generic and recent:
                        evidence_match = PRODUCT.search(norm(text))
                        pos = (
                            evidence_match.start()
                            if evidence_match else 0
                        )
                        evidence = re.sub(
                            r"\s+", " ",
                            text[max(0, pos - 35):pos + 100],
                        )
                        found[final] = dict(
                            source=name,
                            buyer=name,
                            title=title,
                            url=final,
                            published=date_value,
                            deadline="",
                            value="",
                            cpv="",
                            reference="",
                            kind="Moguća nabava — provjeriti dokumentaciju",
                            status="",
                            region=source.get(
                                "region", "Područje praćenja"
                            ),
                            evidence=evidence,
                        )

                if soup:
                    links = candidate_links(soup, final, procurement)

                    if url == start:
                        home = session.get(final, timeout=(12, 25))
                        home.raise_for_status()
                        links.update(candidate_links(
                            BeautifulSoup(home.content, "html.parser"),
                            final,
                            procurement,
                        ))

                    for target, meta in links.items():
                        target_domain = (
                            urlparse(target).netloc.lower()
                            .removeprefix("www.")
                        )
                        if target_domain != domain:
                            continue

                        if (
                            target not in seen
                            and target not in [q[0] for q in queue]
                        ):
                            queue.append((
                                target,
                                meta["title"],
                                meta["context"],
                            ))

            except Exception as e:
                errors.append(
                    f"{url}: {type(e).__name__}: "
                    f"{str(e).splitlines()[0][:100]}"
                )

        if queue:
            errors.append(
                f"Preostalo {len(queue)} poveznica; "
                "dosegnut vremenski/brojčani limit"
            )

    if len(seen) <= 1 and not found:
        errors.append(
            "Nije potvrđen zaseban popis nabave; "
            "potrebna provjera adrese"
        )

    state = (
        "NEPOTPUNO" if errors
        else "PREGLEDANO — AUTOMATSKI ODABRANE POVEZNICE"
    )
    return list(found.values()), source_status(
        name, state, len(seen), "; ".join(errors[:5])
    )


def build_report(items, coverage, previous, today, initial):
    unique = {}
    for item in items:
        key = (
            item["url"] + "|"
            + item["reference"] + "|"
            + item["kind"]
        )
        unique[key] = item

    changes, new_seen = [], dict(previous)
    for key, item in unique.items():
        digest = signature(item)
        if previous.get(key) != digest:
            change = (
                "IZMJENA" if key in previous
                else ("POČETNI PREGLED" if initial else "NOVO U PRAĆENJU")
            )
            changes.append(dict(item, change=change))
        new_seen[key] = digest

    changes.sort(key=lambda i: (
        not bool(REGION.search(
            norm(i["buyer"] + " " + i["region"])
        )),
        i["published"],
    ))

    failures = sum(
        "NEPOTPUNO" in c["status"] for c in coverage
    )
    lines = [
        f"Pregled natječaja — {today:%d.%m.%Y.}",
        f"Novih/izmijenjenih kandidata: {len(changes)}. "
        f"Izvora s nepotpunim pregledom: {failures}.",
        "Obuhvat: EOJN za cijelu RH; mrežne stranice iz registra "
        "za dvije županije.",
        "Registar ustanova još nije potvrđen kao iscrpan. "
        "PREGLEDANO na mrežnoj stranici znači samo da su "
        "obrađene otkrivene poveznice.",
        "",
    ]

    if initial:
        lines += [
            "Prvo pokretanje: početni pregled; objave bez "
            "potvrđenog datuma nisu označene kao objavljene danas.",
            "",
        ]

    if not changes:
        lines += [
            "Nema novih automatski prepoznatih kandidata. "
            "To nije potvrda da na nepročitanim izvorima nema natječaja.",
            "",
        ]

    for item in changes:
        lines += [
            f"{item['change']}: {item['title']}",
            f"Naručitelj: {item['buyer']}",
            f"Vrsta/status: {item['kind']} / "
            f"{item['status'] or 'nije potvrđen'}",
            f"Objavljeno: {item['published'] or 'datum nije potvrđen'}",
            f"Rok: {item['deadline'] or 'provjeriti u dokumentaciji'}",
            f"Procijenjena vrijednost (EUR): "
            f"{item['value'] or 'nije potvrđena'}",
            f"CPV / evidencijski broj: {item['cpv'] or '—'} / "
            f"{item['reference'] or '—'}",
            item["url"],
            "",
        ]

    lines += ["STATUS IZVORA"]
    for c in coverage:
        lines.append(
            f"{c['status']} | {c['source']} | "
            f"{c['count']} stavki/stranica | {c['detail']}"
        )

    lines += [
        "",
        "Izdvajanje koristi ključne riječi i CPV. "
        "Skenirani PDF-ovi, nepodržani privitci, zatvorene objave "
        "i stavke bez prepoznatljivog naslova "
        "mogu zahtijevati ručnu provjeru.",
    ]
    return "\n".join(lines), changes, new_seen


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--send", action="store_true")
    parser.add_argument("--skip-eojn", action="store_true")
    parser.add_argument("--source-limit", type=int, default=0)
    args = parser.parse_args()

    now = datetime.now(TZ)
    out = ROOT / "reports"
    out.mkdir(exist_ok=True)

    state_path = ROOT / "state" / "seen.json"
    state = (
        json.loads(state_path.read_text(encoding="utf-8"))
        if state_path.exists() else {}
    )
    initial = not state.get("seen")

    since = (now.date() - timedelta(days=7)).isoformat()
    if state.get("last_sent"):
        since = (
            date.fromisoformat(state["last_sent"])
            - timedelta(days=2)
        ).isoformat()

    items, coverage = [], []

    if not args.skip_eojn:
        try:
            items, coverage = collect_eojn(since)
        except Exception as e:
            coverage = [source_status(
                "EOJN",
                "NEPOTPUNO",
                detail=(
                    type(e).__name__ + ": "
                    + str(e).splitlines()[0][:150]
                ),
            )]
    else:
        coverage.append(source_status(
            "EOJN",
            "NEPOTPUNO",
            detail="Preskočen radi provjere drugih izvora",
        ))

    sources = yaml.safe_load(
        (ROOT / "sources.yml").read_text(encoding="utf-8")
    )["sources"]

    if args.source_limit:
        sources = sources[:args.source_limit]

    with ThreadPoolExecutor(max_workers=6) as pool:
        for found, status in pool.map(
            lambda s: scan_site(s, now.date()), sources
        ):
            items.extend(found)
            coverage.append(status)
            print(
                f"{status['source']}: "
                f"{status['status']} ({status['count']})",
                flush=True,
            )

    body, changes, seen = build_report(
        items,
        coverage,
        state.get("seen", {}),
        now.date(),
        initial,
    )

    (out / "izvjestaj.txt").write_text(
        body, encoding="utf-8"
    )
    (out / "izvjestaj.html").write_text(
        '<!doctype html><meta charset="utf-8">'
        '<pre style="white-space:pre-wrap;font:16px sans-serif">'
        + html.escape(body) + "</pre>",
        encoding="utf-8",
    )
    (out / "rezultati.json").write_text(
        json.dumps(
            dict(
                generated=now.isoformat(),
                changes=changes,
                coverage=coverage,
            ),
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )

    if args.send:
        if args.skip_eojn or args.source_limit:
            raise RuntimeError(
                "Slanje ograničenog testnog pregleda nije dopušteno"
            )

        sender = os.getenv("SMTP_USER")
        recipient = os.getenv("REPORT_TO")
        password = os.getenv("SMTP_PASSWORD")

        if not all((sender, recipient, password)):
            raise RuntimeError(
                "Izvještaj spremljen, ALI NIJE POSLAN: "
                "nedostaju SMTP postavke / GMAIL_APP_PASSWORD"
            )

        msg = EmailMessage()
        incomplete = any(
            "NEPOTPUNO" in c["status"] for c in coverage
        )
        msg["Subject"] = (
            ("[NEPOTPUN PREGLED] " if incomplete else "")
            + "Natječaji — " + now.strftime("%d.%m.%Y.")
        )
        msg["From"] = sender
        msg["To"] = recipient
        msg.set_content(body)

        with smtplib.SMTP_SSL(
            "smtp.gmail.com", 465, timeout=45
        ) as smtp:
            smtp.login(sender, password.replace(" ", ""))
            refused = smtp.send_message(msg)
            if refused:
                raise RuntimeError(
                    "Poslužitelj nije prihvatio primatelja"
                )

        state_path.parent.mkdir(exist_ok=True)
        updated = dict(
            seen=seen,
            last_sent=state.get("last_sent"),
        )
        if all(
            c["status"] == "PREGLEDANO"
            for c in coverage
            if c["source"].startswith("EOJN")
        ):
            updated["last_sent"] = now.date().isoformat()

        state_path.write_text(
            json.dumps(updated, ensure_ascii=False),
            encoding="utf-8",
        )
        print(
            "SMTP poslužitelj prihvatio je izvještaj. "
            "Provjerite primitak u poštanskom sandučiću."
        )

    else:
        print(
            "Probni pregled završen. E-mail nije poslan; "
            "stanje poslanih objava nije promijenjeno."
        )


if __name__ == "__main__":
    main()
