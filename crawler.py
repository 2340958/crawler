import argparse
import asyncio
import aiohttp
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse, urldefrag, quote, unquote, urlunparse
import time
import random
from collections import defaultdict
import html
import datetime
import psutil
import csv
import ssl

from rich.console import Console
from rich.live import Live
from rich.table import Table
from rich.text import Text

# Initialize rich console
console = Console()

# --- Configuration Constants ---
DEFAULT_MAX_DEPTH = 6
DEFAULT_TIMEOUT = 20
DEFAULT_EXCLUDED_URLS = ['https://www.example.com/',
                         'https://*.example.com/'] #pattern: 'http://www.example.com','https://*.example.com/','*.example.com'
SEM_LIMIT = 4
MAX_RETRIES = 3 # Max retries for a single fetch in fetch_with_retries
RETRY_BACKOFF = 5
TCP_CONNECTIONS_LIMIT = 100
CONNECTION_KEEPALIVE = 20
ASYNC_PHASE_TIMEOUT = 300 # 5 minutes default
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.1.1 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:89.0) Gecko/20100101 Firefox/89.0",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 14_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.0.3 Mobile/15E148 Safari/604.1"
]
DEFAULT_REQUEST_DELAY_MIN = 0.2
DEFAULT_REQUEST_DELAY_MAX = 0.8

HTTP_STATUS_CODE_EXPLANATIONS_DE = {
    # Client Errors 4xx
    400: "Ungültige Anfrage. Der Server konnte die Anfrage aufgrund eines Client-Fehlers nicht verstehen (z.B. fehlerhafte Anfragesyntax).",
    401: "Nicht autorisiert. Die Anfrage erfordert eine Benutzerauthentifizierung.",
    403: "Verboten. Der Server hat die Anfrage verstanden, verweigert jedoch die Autorisierung. Der Zugriff ist dauerhaft verboten und wird nicht gewährt.",
    404: "Nicht gefunden. Der Server konnte die angeforderte Ressource nicht finden.",
    405: "Methode nicht erlaubt. Die in der Anfrage angegebene Methode ist für die angeforderte Ressource nicht zulässig.",
    406: "Accept Header der Applikation nicht supported von der Webseite.",
    408: "Zeitüberschreitung der Anfrage. Der Server hat die Anfrage nicht innerhalb der Zeit erhalten, die er bereit war zu warten.",
    410: "Verschwunden. Die angeforderte Ressource ist nicht mehr verfügbar und wurde dauerhaft entfernt.",
    429: "Zu viele Anfragen. Der Benutzer hat in einem bestimmten Zeitraum zu viele Anfragen gesendet ('Rate Limiting').",
    # Server Errors 5xx
    500: "Interner Serverfehler. Der Server ist auf eine unerwartete Bedingung gestoßen, die ihn daran gehindert hat, die Anfrage zu erfüllen.",
    502: "Ungültiges Gateway. Der Server hat als Gateway oder Proxy eine ungültige Antwort von einem Upstream-Server erhalten.",
    503: "Dienst nicht verfügbar. Der Server ist derzeit nicht in der Lage, die Anfrage zu bearbeiten (z.B. wegen Überlastung oder Wartung).",
    504: "Gateway-Zeitüberschreitung. Der Server hat als Gateway oder Proxy keine rechtzeitige Antwort von einem Upstream-Server erhalten.",
    # Custom/Non-Standard Statuses from your script
    "Timeout": "Zeitüberschreitung der Anfrage. Es konnte innerhalb des festgelegten Zeitlimits keine Antwort vom Server empfangen werden.",
    "ConnectionError": "Verbindungsfehler. Es konnte keine Verbindung zum Server hergestellt werden (z.B. DNS-Problem, Server nicht erreichbar).",
    "InvalidURL": "Ungültige URL. Das Format der URL ist fehlerhaft.",
    "FetchFailedAllRetries": "Fehler beim Abrufen nach allen Wiederholungsversuchen. Die URL konnte auch nach mehreren Versuchen nicht erfolgreich geladen werden.",
    "Exception: ClientOSError": "Fehler in Library aiohttp - Exception: ClientOSError ist ein Verbindungsproblem von aiohttp mit dem Zielserver. Programmspezifisch. Taucht u.a. auf *.admin.ch Seiten auf.",
}
crawl_error_prefixed_explanations = {f"CrawlError: {k}": v for k, v in HTTP_STATUS_CODE_EXPLANATIONS_DE.items() if isinstance(k, str)}
HTTP_STATUS_CODE_EXPLANATIONS_DE.update(crawl_error_prefixed_explanations)
HTTP_STATUS_CODE_EXPLANATIONS_DE.update({
    "CrawlError: AttributeError": "Programmfehler (AttributeError). Ein interner Fehler ist beim Verarbeiten der Seite aufgetreten.",
    "CrawlError: TypeError": "Programmfehler (TypeError). Ein interner Fehler ist beim Verarbeiten der Seite aufgetreten.",
    "CrawlError: ClientOSError": "Client Betriebssystemfehler. Ein Fehler auf Client-Seite im Zusammenhang mit dem Betriebssystem ist aufgetreten (oft Netzwerkbezogen).",
    "Exception: NonHttpUrlRedirectClientError": "Nicht-HTTP-URL Weiterleitungsfehler. Eine Weiterleitung zu einer URL mit einem nicht unterstützten Schema (z.B. 'ftp://', 'file://') wurde festgestellt.",
    "Exception: ClientOSError": "Client Betriebssystemfehler. Ein Fehler auf Client-Seite im Zusammenhang mit dem Betriebssystem ist aufgetreten (oft Netzwerkbezogen)." # Added from your example
})

# --- Global Statistics Variables ---
stats = {
    "crawled_pages": 0, "broken_links": 0, "non_html_pages": 0,
    "cancelled_tasks": 0, "successful_fetches": 0, "failed_fetches": 0,
    "ignored_403s": 0 # NEW: Counter for ignored 403 errors
}
failed_urls_for_retry = []
invalid_links_report = []
crawled_urls_set = set()
checked_external_links_set = set()
error_types_summary = defaultdict(int)
error_links_by_domain_report = defaultdict(list)
all_processed_links_log = []

# --- Global for Rich Table Timing ---
main_queue = None
overall_start_time = 0

# --- Helper Functions ---
async def monitor_resources(interval=5):
    p = psutil.Process()
    while True:
        try:
            memory_info = psutil.virtual_memory(); cpu_percent = psutil.cpu_percent(interval=None)
            open_fds_process = 0
            try: open_fds_process = len(p.connections(kind='inet'))
            except psutil.NoSuchProcess: console.log("[RESOURCE] Monitor: Process no longer exists."); break
            except Exception as e_con: console.log(f"[RESOURCE] Monitor: Error getting connections: {e_con}")
            console.log(f"[RESOURCE] CPU: {cpu_percent:.1f}%, Memory: {memory_info.percent:.1f}% used, NetConns: {open_fds_process}")
            await asyncio.sleep(interval)
        except asyncio.CancelledError: console.log("[RESOURCE] Monitor task cancelled."); break
        except Exception as e: console.log(f"[RESOURCE] Error in monitor: {e}"); await asyncio.sleep(interval * 2)

def sanitize_url(url: str) -> str:
    """
    Sanitizes and normalizes a URL by percent-encoding the path and query
    to handle special characters correctly, while preserving the URL structure.
    """
    try:
        # 1. Remove fragment
        url_no_frag, _ = urldefrag(url)
        
        # 2. Parse the URL into its components
        parsed = urlparse(url_no_frag)
        
        # 3. Percent-encode the path and query components to make them URL-safe.
        # This is the key fix for 400 errors caused by special characters.
        safe_path = quote(parsed.path, safe='/%:')
        safe_query = quote(parsed.query, safe='&=?')

        # 4. Reconstruct the URL from the sanitized components.
        return urlunparse((
            parsed.scheme,
            parsed.netloc,
            safe_path,
            parsed.params, # Usually empty, but preserved for correctness
            safe_query,
            '' # Fragment is already removed
        ))
    except ValueError:
        # Fallback for malformed URLs.
        return urldefrag(url)[0]

def ensure_scheme(url_str: str, default_scheme="https://") -> str:
    parsed = urlparse(url_str)
    if not parsed.scheme:
        url_str_no_proto_relative = url_str.lstrip('/')
        return f"{default_scheme.rstrip('://')}://{url_str_no_proto_relative}"
    return url_str

def is_external(url, base_url):
    return urlparse(url).netloc and urlparse(url).netloc != urlparse(base_url).netloc

def log_processed_link(url, status, content_type, depth, origin_url, is_external_flag, error_msg=None, final_url=None):
    all_processed_links_log.append({
        "timestamp": datetime.datetime.now().isoformat(), "original_url": url, "final_url": final_url or url,
        "status": str(status), "content_type": content_type or "N/A", "depth": depth,
        "origin_url": origin_url or "N/A", "is_external": is_external_flag, "error_message": error_msg or ""})

def sanitize_header_value(value: str) -> str:
    """
    Strips characters that are illegal in HTTP header values,
    including control characters like newlines, carriage returns, and tabs.
    It encodes to latin-1 and decodes back to handle/remove high-bit characters
    that might be present and invalid.
    """
    if not isinstance(value, str):
        return ""
    stripped_value = value.strip()
   
    no_control_chars = ''.join(c for c in stripped_value if ord(c) >= 32)
   
    try:
        safe_value = no_control_chars.encode('latin-1', 'ignore').decode('latin-1')
    except (UnicodeEncodeError, UnicodeDecodeError):
        safe_value = ''.join(c for c in no_control_chars if ord(c) < 127) # Pure 7-bit ASCII

    return safe_value

# --- Core Fetching and Crawling Logic ---
async def fetch_with_retries(
    session: aiohttp.ClientSession, url: str, timeout: int,
    sem: asyncio.Semaphore, verbose: bool, custom_headers: dict = None
):
    # If no custom headers are passed, generate some default realistic ones.
    req_headers = custom_headers if custom_headers else get_realistic_headers()

    async with sem:
        for attempt in range(1, MAX_RETRIES + 1):
            response_obj = None
            try:
                url_to_fetch = url if urlparse(url).scheme else ensure_scheme(url)
                response_obj = await session.get(
                    url_to_fetch,
                    timeout=aiohttp.ClientTimeout(total=timeout),
                    allow_redirects=True,
                    headers=req_headers
                )
                return str(response_obj.url), response_obj, response_obj.status
            except aiohttp.ClientResponseError as e:
                if verbose: console.log(f"[HTTP ERROR] Att {attempt}/{MAX_RETRIES} - Status {e.status} for {str(e.request_info.url)}. History: {e.history if hasattr(e, 'history') else 'N/A'}")
                return str(e.request_info.url), None, e.status
            # ... (rest of the exception handling is the same as the previous version) ...
            except asyncio.TimeoutError:
                if verbose: console.log(f"[TIMEOUT] Att {attempt}/{MAX_RETRIES} for {url}")
                if attempt == MAX_RETRIES: return url, None, "Timeout"
            except aiohttp.ClientConnectorError as e:
                if verbose: console.log(f"[CONNECTION ERR] Att {attempt}/{MAX_RETRIES} for {url}: {type(e).__name__}")
                if attempt == MAX_RETRIES: return url, None, "ConnectionError"
            except aiohttp.InvalidURL:
                if verbose: console.log(f"[INVALID URL] {url}"); return url, None, "InvalidURL"
            except aiohttp.ClientOSError as e:
                if verbose: console.log(f"[ClientOSError] Att {attempt}/{MAX_RETRIES} for {url}: {e}")
                if attempt == MAX_RETRIES: return url, None, "Exception: ClientOSError"
            except aiohttp.ClientError as e: 
                 if verbose: console.log(f"[AIOHTTP ClientError] Att {attempt}/{MAX_RETRIES} for {url}: {type(e).__name__} - {e}")
                 if attempt == MAX_RETRIES: return url, None, f"Exception: {type(e).__name__}"
            except asyncio.CancelledError:
                if verbose: console.log(f"[TASK CANCELLED] Fetching {url}")
                if response_obj: await response_obj.release(); raise
            except Exception as e:
                if verbose: console.log(f"[UNEXPECTED FETCH ERR] Att {attempt}/{MAX_RETRIES} for {url}: {type(e).__name__} - {str(e)}")
                if attempt == MAX_RETRIES: return url, None, f"Exception: {type(e).__name__}"
            if attempt < MAX_RETRIES: await asyncio.sleep(RETRY_BACKOFF * attempt * random.uniform(0.8, 1.2))
        return url, None, "FetchFailedAllRetries"

async def crawl_and_check(
    session: aiohttp.ClientSession, initial_sanitized_base_url: str, max_depth: int,
    excluded_urls: list, sem: asyncio.Semaphore, queue: asyncio.Queue, verbose: bool,
    delay_min: float, delay_max: float, ignore_403: bool
):
    p_initial_base_url_netloc = urlparse(initial_sanitized_base_url).netloc
    try:
        while True:
            fetched_response_obj = None
            queue_item = await queue.get()
            if queue_item is None: queue.task_done(); break
            current_url_from_queue, current_depth, parent_url_where_found = queue_item
            try:
                is_retry_item = any(url == current_url_from_queue for url, _, _ in failed_urls_for_retry)
                if current_url_from_queue in crawled_urls_set and not is_retry_item:
                    if verbose: console.log(f"[SKIP] Already processed: {current_url_from_queue} (From: {parent_url_where_found})")
                    continue
                if current_depth > max_depth:
                    if verbose: console.log(f"[SKIP] Max depth ({max_depth}) for: {current_url_from_queue} (From: {parent_url_where_found})")
                    log_processed_link(current_url_from_queue, "DepthExceeded", None, current_depth, parent_url_where_found, False)
                    continue
                crawled_urls_set.add(current_url_from_queue); stats["crawled_pages"] += 1
                if verbose: console.log(f"Crawling: {current_url_from_queue} (Depth: {current_depth}, From: {parent_url_where_found})")
                
                # Generate realistic headers for the internal page fetch
                internal_page_headers = get_realistic_headers(
                    referer=parent_url_where_found if parent_url_where_found != "INITIAL_BASE_URL" else None
                )
                
                page_being_crawled_final_url, fetched_response_obj, fetch_status = await fetch_with_retries(
                    session, current_url_from_queue, DEFAULT_TIMEOUT, sem, verbose, custom_headers=internal_page_headers)
                content_type = fetched_response_obj.headers.get('Content-Type', '').lower() if fetched_response_obj else None
                log_processed_link(current_url_from_queue, fetch_status, content_type, current_depth, parent_url_where_found, False, final_url=page_being_crawled_final_url)

                if fetched_response_obj is None or not (200 <= int(fetch_status) < 300 if isinstance(fetch_status, int) else False):
                    if fetch_status == 403 and ignore_403:
                        stats["ignored_403s"] += 1
                        if verbose: console.log(f"[IGNORING 403] For internal URL: {current_url_from_queue}")
                        if fetched_response_obj: await fetched_response_obj.release()
                        continue
                    stats["broken_links"] += 1
                    invalid_links_report.append((parent_url_where_found, current_url_from_queue, page_being_crawled_final_url, fetch_status))
                    error_types_summary[str(fetch_status)] += 1
                    error_links_by_domain_report[urlparse(page_being_crawled_final_url).netloc].append((parent_url_where_found, current_url_from_queue, page_being_crawled_final_url, fetch_status))
                    if fetch_status in ("Timeout", "ConnectionError") or (isinstance(fetch_status, int) and fetch_status >= 500):
                        if verbose: console.log(f"[RETRY QUEUE] Adding: {current_url_from_queue} (Status: {fetch_status}, From: {parent_url_where_found})")
                        failed_urls_for_retry.append((current_url_from_queue, current_depth, parent_url_where_found))
                    else: stats["failed_fetches"] +=1
                    if fetched_response_obj: await fetched_response_obj.release()
                    continue
                stats["successful_fetches"] +=1
                if 'text/html' in (content_type or ""):
                    html_content = await fetched_response_obj.text(); await fetched_response_obj.release()
                    soup = BeautifulSoup(html_content, 'html.parser')
                    for link_tag in soup.find_all(['a', 'link'], href=True):
                        href_val = link_tag.get('href');
                        if not href_val: continue
                        abs_link = urljoin(page_being_crawled_final_url, href_val.strip()); resolved_sanitized_href = sanitize_url(abs_link)
                        is_excluded = False
                        if resolved_sanitized_href.startswith(('tel:', 'mailto:', 'javascript:')): is_excluded = True
                        else:
                            parsed_url_to_check = None; hostname_to_check = ""; scheme_to_check = ""
                            try:
                                url_for_parsing = ensure_scheme(resolved_sanitized_href)
                                parsed_url_to_check = urlparse(url_for_parsing)
                                hostname_to_check = parsed_url_to_check.netloc.lower()
                                scheme_to_check = parsed_url_to_check.scheme.lower()
                            except ValueError:
                                if verbose: console.log(f"[EXCL CHECK ERR] Cannot parse for exclusion: {resolved_sanitized_href}")
                            if parsed_url_to_check:
                                for excluded_pattern_orig in excluded_urls:
                                    parsed_excluded_pattern_obj = None; excluded_hostname_main_part = ""; excluded_scheme_pattern = ""; is_host_wildcard_pattern = False
                                    try:
                                        temp_pattern_for_parse = excluded_pattern_orig
                                        _parsed_temp_pattern = urlparse(ensure_scheme(temp_pattern_for_parse))
                                        if _parsed_temp_pattern.netloc and _parsed_temp_pattern.netloc.startswith("*."):
                                            is_host_wildcard_pattern = True
                                            excluded_hostname_main_part = _parsed_temp_pattern.netloc[2:].lower()
                                            excluded_scheme_pattern = _parsed_temp_pattern.scheme.lower() if _parsed_temp_pattern.scheme else ""
                                            parsed_excluded_pattern_obj = _parsed_temp_pattern
                                        elif not _parsed_temp_pattern.netloc and temp_pattern_for_parse.startswith("*."):
                                            is_host_wildcard_pattern = True
                                            _parsed_temp_pattern_wc = urlparse("//" + temp_pattern_for_parse.replace("*.", "dummy.", 1))
                                            excluded_hostname_main_part = _parsed_temp_pattern_wc.netloc.replace("dummy.","").lower()
                                            excluded_scheme_pattern = "" 
                                            parsed_excluded_pattern_obj = _parsed_temp_pattern_wc
                                        else: parsed_excluded_pattern_obj = _parsed_temp_pattern
                                    except ValueError:
                                        if verbose: console.log(f"[EXCL PATTERN ERR] Cannot parse pattern: {excluded_pattern_orig}"); continue
                                    matched = False
                                    if is_host_wildcard_pattern:
                                        scheme_match = (not excluded_scheme_pattern or scheme_to_check == excluded_scheme_pattern)
                                        host_match = (hostname_to_check == excluded_hostname_main_part or hostname_to_check.endswith("." + excluded_hostname_main_part))
                                        if scheme_match and host_match:
                                            pattern_path = parsed_excluded_pattern_obj.path
                                            if pattern_path and pattern_path != "/":
                                                if parsed_url_to_check.path.startswith(pattern_path): matched = True
                                            else: matched = True
                                    elif resolved_sanitized_href.startswith(excluded_pattern_orig): matched = True
                                    if matched:
                                        is_excluded = True
                                        if verbose: console.log(f"[EXCLUDING] URL '{resolved_sanitized_href}' matches pattern '{excluded_pattern_orig}'")
                                        break
                        if is_excluded: continue
                        if is_external(resolved_sanitized_href, initial_sanitized_base_url):
                            if resolved_sanitized_href not in checked_external_links_set:
                                checked_external_links_set.add(resolved_sanitized_href)
                                if verbose: console.log(f"Checking external: {resolved_sanitized_href} (Found on: {page_being_crawled_final_url})")
                                
                                # Generate specific, realistic headers for this external link fetch
                                external_link_fetch_headers = get_realistic_headers(
                                    referer=page_being_crawled_final_url
                                )
                                
                                ext_final_url, ext_resp_obj, ext_status = await fetch_with_retries(session, resolved_sanitized_href, DEFAULT_TIMEOUT, sem, verbose, custom_headers=external_link_fetch_headers)
                                ext_content_type = ext_resp_obj.headers.get('Content-Type', '').lower() if ext_resp_obj else None
                                log_processed_link(resolved_sanitized_href, ext_status, ext_content_type, current_depth + 1, page_being_crawled_final_url, True, final_url=ext_final_url)
                                if ext_resp_obj is None or not (200 <= int(ext_status) < 300 if isinstance(ext_status, int) else False):
                                    if ext_status == 403 and ignore_403:
                                        stats["ignored_403s"] += 1
                                        if verbose: console.log(f"[IGNORING 403] For external URL: {resolved_sanitized_href}")
                                        if ext_resp_obj: await ext_resp_obj.release()
                                        continue
                                    stats["broken_links"] += 1
                                    invalid_links_report.append((page_being_crawled_final_url, resolved_sanitized_href, ext_final_url, ext_status))
                                    error_types_summary[str(ext_status)] += 1
                                    error_links_by_domain_report[urlparse(ext_final_url).netloc].append((page_being_crawled_final_url, resolved_sanitized_href, ext_final_url, ext_status))
                                    stats["failed_fetches"] +=1
                                else: stats["successful_fetches"] +=1
                                if ext_resp_obj: await ext_resp_obj.release()
                        else: # Internal link
                            if urlparse(resolved_sanitized_href).netloc == p_initial_base_url_netloc:
                                 if resolved_sanitized_href not in crawled_urls_set and current_depth < max_depth :
                                    if verbose: console.log(f"[QUEUEING INTERNAL] Adding: {resolved_sanitized_href} (Depth: {current_depth + 1}, From: {page_being_crawled_final_url})")
                                    await queue.put((resolved_sanitized_href, current_depth + 1, page_being_crawled_final_url))
                else:
                    stats["non_html_pages"] += 1
                    if verbose: console.log(f"Skipping non-HTML: {page_being_crawled_final_url} (Type: {content_type})")
                    if fetched_response_obj: await fetched_response_obj.release()
                if delay_max > 0: await asyncio.sleep(random.uniform(delay_min, delay_max))
            except asyncio.CancelledError:
                stats["cancelled_tasks"] += 1; console.log(f"[CANCELLED] Item processing for {current_url_from_queue} cancelled.")
                if fetched_response_obj and not fetched_response_obj.closed: await fetched_response_obj.release(); raise
            except Exception as e:
                console.log(f"[ERROR] Crawl exception for {current_url_from_queue} (From: {parent_url_where_found}): {type(e).__name__} - {str(e)}")
                invalid_links_report.append((parent_url_where_found, current_url_from_queue, current_url_from_queue, f"CrawlError: {type(e).__name__}"))
                stats["broken_links"] +=1; stats["failed_fetches"] +=1; error_types_summary[f"CrawlError: {type(e).__name__}"] += 1
                if fetched_response_obj and not fetched_response_obj.closed: await fetched_response_obj.release()
            finally: queue.task_done()
    except asyncio.CancelledError: console.log(f"[WORKER] Worker task itself cancelled.")
    except Exception as e: console.log(f"[WORKER] Unhandled exception in worker's main loop: {type(e).__name__} - {e}")
    finally:
        if verbose: console.log(f"[WORKER] Worker exiting.")

# --- Reporting Functions ---
def generate_html_report(start_time_param, base_url_for_report_name: str, max_depth_arg: int, excluded_urls_arg: list, timeout_arg: int, ignore_403_flag: bool):
    runtime = time.time() - start_time_param; report_date = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    parsed_report_base = urlparse(base_url_for_report_name)
    domain_file_part = parsed_report_base.netloc.replace("www.", "").replace(".", "_") if parsed_report_base.netloc else "unknown_site"
    report_filename = f"broken_links_report_{domain_file_part}_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
    with open(report_filename, "w", encoding="utf-8") as rf:
        rf.write("<html><head><title>Broken Links Report</title><style>body{font-family:sans-serif;margin:20px}h1,h2,h3{color:#333}table{border-collapse:collapse;width:100%;margin-bottom:20px}th,td{border:1px solid #ddd;padding:8px;text-align:left;word-break:break-all}th{background-color:#f2f2f2}li{margin-bottom:5px}.error{color:red;font-weight:bold} .status-code{cursor:help;border-bottom:1px dotted black}</style></head><body>")
        rf.write(f"<h1>Broken Links Report for {html.escape(base_url_for_report_name)}</h1><p>Generated: {report_date}</p><p>Runtime: {format_elapsed_time(runtime)}</p>")
        rf.write(f"<h2>Parameters</h2><ul><li>Base URL: {html.escape(base_url_for_report_name)}</li><li>Max Depth: {max_depth_arg}</li><li>Timeout: {timeout_arg}s</li><li>Excluded: {html.escape(', '.join(excluded_urls_arg) or 'None')}</li><li>Ignoring 403 Errors: {'Yes' if ignore_403_flag else 'No'}</li></ul>") # NEW: Parameter in report
        rf.write(f"<h2>Summary</h2><ul><li>Internal Pages Processed: {stats['crawled_pages']}</li><li>External Links Checked: {len(checked_external_links_set)}</li><li>Successful Fetches: {stats['successful_fetches']}</li><li>Broken/Failed: <span class='error'>{stats['broken_links']}</span></li>")
        if ignore_403_flag: rf.write(f"<li>Ignored 403 (Forbidden) Errors: {stats['ignored_403s']}</li>") # NEW: Summary stat
        rf.write(f"<li>Non-HTML: {stats['non_html_pages']}</li></ul>")
        rf.write("<h2>Error Summary by Type</h2><ul>")
        if error_types_summary:
            for err_type, count in sorted(error_types_summary.items()):
                status_key = err_type; 
                try: status_key = int(err_type)
                except ValueError: pass
                explanation = HTTP_STATUS_CODE_EXPLANATIONS_DE.get(status_key)
                if explanation is None and isinstance(status_key, str) and status_key.startswith("Exception: "):
                    generic_exception_type = status_key.split(':')[0]
                    specific_exception_name = status_key
                    explanation = HTTP_STATUS_CODE_EXPLANATIONS_DE.get(specific_exception_name, HTTP_STATUS_CODE_EXPLANATIONS_DE.get(generic_exception_type, f"Spezifischer Fehler: {html.escape(str(status_key))}"))
                elif explanation is None: explanation = "Keine spezifische Erklärung verfügbar."
                escaped_explanation = html.escape(explanation)
                rf.write(f"<li><span class='status-code' title='{escaped_explanation}'>{html.escape(str(err_type))}</span>: {count} occurrences</li>")
        else: rf.write("<li>No errors recorded.</li>")
        rf.write("</ul><h2>Invalid Links Details (Grouped by Domain of Final Failed URL)</h2>")
        if error_links_by_domain_report:
            for domain, links_data in sorted(error_links_by_domain_report.items()):
                rf.write(f"<h3>Domain: {html.escape(domain)} ({len(links_data)} broken)</h3><ul>")
                for page_on, orig_href, final_url, err_code in links_data:
                    rf.write(f"<li>On Page: <a href='{html.escape(page_on)}' target='_blank'>{html.escape(page_on)}</a><br>")
                    if orig_href != final_url: rf.write(f"     Original Link: <a href='{html.escape(orig_href)}' target='_blank'>{html.escape(orig_href)}</a><br>")
                    status_key_detail = err_code; 
                    try: status_key_detail = int(err_code)
                    except (ValueError, TypeError): pass
                    explanation_detail = HTTP_STATUS_CODE_EXPLANATIONS_DE.get(status_key_detail)
                    if explanation_detail is None and isinstance(status_key_detail, str) and status_key_detail.startswith("Exception: "):
                        generic_exception_type_detail = status_key_detail.split(':')[0]
                        specific_exception_name_detail = status_key_detail
                        explanation_detail = HTTP_STATUS_CODE_EXPLANATIONS_DE.get(specific_exception_name_detail, HTTP_STATUS_CODE_EXPLANATIONS_DE.get(generic_exception_type_detail, f"Spezifischer Fehler: {html.escape(str(status_key_detail))}"))
                    elif explanation_detail is None: explanation_detail = "Keine spezifische Erklärung verfügbar."
                    escaped_explanation_detail = html.escape(explanation_detail)
                    rf.write(f"     Final URL (Failed): <a href='{html.escape(final_url)}' target='_blank'>{html.escape(final_url)}</a><br>")
                    rf.write(f"     Status/Error: <span class='error status-code' title='{escaped_explanation_detail}'>{html.escape(str(err_code))}</span></li><br>")
                rf.write("</ul>")
        else: rf.write("<p>No broken links found.</p>")
        rf.write("</body></html>")
    console.print(f"HTML Report: [blue]{report_filename}[/blue]")

def generate_csv_log(base_url_for_report_name: str):
    parsed_report_base = urlparse(base_url_for_report_name)
    domain_file_part = parsed_report_base.netloc.replace("www.", "").replace(".", "_") if parsed_report_base.netloc else "unknown_site"
    log_filename = f"visited_links_{domain_file_part}_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
    if not all_processed_links_log: console.print("No links processed, CSV log empty."); return
    fieldnames = ["timestamp", "original_url", "final_url", "status", "content_type", "depth", "origin_url", "is_external", "error_message"]
    with open(log_filename, "w", newline='', encoding="utf-8") as csvf:
        writer = csv.DictWriter(csvf, fieldnames=fieldnames, extrasaction='ignore')
        writer.writeheader(); writer.writerows(all_processed_links_log)
    console.print(f"Visited links CSV: [blue]{log_filename}[/blue]")

def format_elapsed_time(seconds: float) -> str:
    if seconds < 0: seconds = 0
    h = int(seconds // 3600); m = int((seconds % 3600) // 60); s = int(seconds % 60)
    return f"{h:02d}:{m:02d}:{s:02d}" if h > 0 else f"{m:02d}:{s:02d}"

def create_rich_table(current_phase: str, current_phase_start_time: float):
    global overall_start_time, failed_urls_for_retry, error_types_summary
    table = Table(title=f"Crawler Status - Phase: {current_phase}")
    table.add_column("Statistic", style="cyan", no_wrap=True); table.add_column("Value", style="magenta", justify="right")
    now = time.time()
    table.add_row("Total Elapsed", format_elapsed_time(now - overall_start_time), style="yellow")
    table.add_row("Phase Elapsed", format_elapsed_time(now - current_phase_start_time), style="yellow")
    table.add_row("--------------------", "----------")
    table.add_row("Internal Pages Processed", str(stats["crawled_pages"]))
    table.add_row("External Links Checked", str(len(checked_external_links_set)))
    table.add_row("Successful Fetches", str(stats["successful_fetches"]))
    table.add_row("Broken Links / Failures", Text(str(stats["broken_links"]), style="bold red" if stats["broken_links"] > 0 else "green"))
    table.add_row("Non-HTML Pages", str(stats["non_html_pages"]))
    num_retry_urls = len(failed_urls_for_retry)
    table.add_row("URLs in Retry Queue", Text(str(num_retry_urls), style="bold red" if num_retry_urls > 0 else "green"))
    if stats["ignored_403s"] > 0:
        table.add_row("Ignored 403s", str(stats["ignored_403s"]), style="dim yellow")
    q_size = "N/A"
    if main_queue:
        try: q_size = str(main_queue.qsize())
        except Exception: pass
    table.add_row("Queue Size (approx)", q_size)
    try:
        table.add_row("CPU Usage", f"{psutil.cpu_percent(interval=None):.1f}%")
        table.add_row("Memory Usage", f"{psutil.virtual_memory().percent:.1f}%")
    except Exception: table.add_row("CPU/Memory", "Error fetching")
    table.add_row("--------------------", "----------")
    table.add_row(Text("Error Summary (Top 5)", style="bold yellow"), "")
    if error_types_summary:
        sorted_errors = sorted(error_types_summary.items(), key=lambda item: item[1], reverse=True)
        for i, (err_type, count) in enumerate(sorted_errors):
            if i >= 5:
                break
            table.add_row(f"  {err_type}", str(count), style="red")
    else:
        table.add_row("  (No errors yet)", "", style="green")
    return table

# --- REPLACE the existing get_realistic_headers function with this one ---

def get_realistic_headers(referer: str = None):
    """
    Generates a dictionary of classic, common browser headers.
    This version omits the Host and Connection headers, letting aiohttp manage them.
    """
    headers = {
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "de, en-US;q=0.9, en;q=0.8",
        "Accept-Encoding": "gzip, deflate",
        "Upgrade-Insecure-Requests": "1",
    }
    
    if referer:
        safe_referer = sanitize_header_value(referer)
        if safe_referer:
            headers["Referer"] = safe_referer
        
    return headers

# --- Main Application ---
async def main_crawler(base_url_arg: str, max_depth: int, excluded_urls_list: list, verbose: bool, req_timeout: int, delay_min: float, delay_max: float, ignore_403: bool): # NEW: ignore_403 flag
    global main_queue, overall_start_time, failed_urls_for_retry, crawled_urls_set
    overall_start_time = time.time()
    base_url_schemed = ensure_scheme(base_url_arg)
    if base_url_schemed != base_url_arg and verbose: console.print(f"[INFO] Base URL auto-schemed: '{base_url_schemed}'.", style="yellow")
    
    main_queue = asyncio.Queue()
    semaphore = asyncio.Semaphore(SEM_LIMIT)
    initial_sanitized_base_url = sanitize_url(base_url_schemed)
    await main_queue.put((initial_sanitized_base_url, 0, "INITIAL_BASE_URL"))
    
    ssl_context = ssl.create_default_context()
    # Add more broadly compatible SSL options to potentially mitigate ClientOSError
    ssl_context.minimum_version = ssl.TLSVersion.TLSv1_2
    ssl_context.set_ciphers('DEFAULT@SECLEVEL=1')
    
    conn = aiohttp.TCPConnector(
        limit_per_host=10, 
        limit=TCP_CONNECTIONS_LIMIT, 
        keepalive_timeout=CONNECTION_KEEPALIVE, 
        ssl=ssl_context
    )
    async with aiohttp.ClientSession(connector=conn) as session:
        res_mon_task = asyncio.create_task(monitor_resources()) if verbose else None
        workers = [asyncio.create_task(crawl_and_check(session, initial_sanitized_base_url, max_depth, excluded_urls_list, semaphore, main_queue, verbose, delay_min, delay_max, ignore_403)) for _ in range(SEM_LIMIT)] # NEW: Pass ignore_403
        
        with Live(create_rich_table("Initializing...", overall_start_time), console=console, auto_refresh=False, refresh_per_second=2) as live:
            phases = ["Initial Crawl", "Retry Phase"] 
            phase_err = None
            for phase_name in phases:
                if phase_err: break
                current_phase_start_time = time.time()
                
                if phase_name == "Retry Phase":
                    if not failed_urls_for_retry:
                        console.print("[INFO] No URLs for retry phase. Skipping.", style="yellow"); continue
                    console.print(f"[INFO] Starting {phase_name} for {len(failed_urls_for_retry)} URLs.", style="bold blue")
                    requeue_items = list(failed_urls_for_retry); failed_urls_for_retry.clear()
                    for url, depth, parent in requeue_items:
                        if url in crawled_urls_set: crawled_urls_set.remove(url)
                        await main_queue.put((url, depth, parent))
                    if main_queue.empty() and requeue_items : console.print("[WARN] Retry queue empty after re-adding items. This is unexpected.", style="yellow")
                elif main_queue.empty() and phase_name == "Initial Crawl": console.print("[ERROR] Initial queue empty.", style="bold red"); break
                
                console.print(f"[PHASE] Starting: {phase_name}"); live.update(create_rich_table(phase_name, current_phase_start_time), refresh=True)
                join_task = asyncio.create_task(main_queue.join())
                phase_timeout_flag = False; phase_monotonic_start_for_timeout = time.monotonic()
                try:
                    while not join_task.done():
                        if main_queue.empty() and all(w.done() for w in workers):
                            console.print(f"[INFO] {phase_name}: Queue empty, workers appear done.", style="dim")
                            if not join_task.done(): join_task.cancel(); break
                        live.update(create_rich_table(phase_name, current_phase_start_time), refresh=True)
                        if ASYNC_PHASE_TIMEOUT > 0 and (time.monotonic() - phase_monotonic_start_for_timeout > ASYNC_PHASE_TIMEOUT):
                            phase_timeout_flag = True; console.print(f"[TIMEOUT] {phase_name} after {ASYNC_PHASE_TIMEOUT}s.", style="bold red")
                            if not join_task.done(): join_task.cancel(); break
                        try: await asyncio.wait_for(asyncio.shield(join_task), timeout=0.5)
                        except asyncio.TimeoutError: pass
                    if phase_timeout_flag: 
                        try: await join_task
                        except asyncio.CancelledError: pass
                        raise asyncio.TimeoutError(f"{phase_name} overall timeout.")
                    await join_task
                    console.print(f"[INFO] {phase_name} completed.", style="green")
                except asyncio.CancelledError: phase_err = asyncio.CancelledError(f"{phase_name} cancelled"); console.print(f"[CANCELLED] {phase_name}.", style="yellow")
                except asyncio.TimeoutError as e: phase_err = e; console.print(f"[ERROR] Timeout during {phase_name}: {e}", style="bold red")
                except Exception as e: phase_err = e; console.print(f"[CRITICAL ERROR] In {phase_name}: {type(e).__name__} - {e}", style="bold red")
                if phase_err: console.print(f"[HALT] Halting further phases due to error in {phase_name}.", style="bold red"); break
        
        console.print("Shutting down workers..."); 
        for _ in workers: await main_queue.put(None)
        for i, res in enumerate(await asyncio.gather(*workers, return_exceptions=True)):
            if isinstance(res, Exception) and not isinstance(res, asyncio.CancelledError): console.print(f"Worker {i} error: {res}", style="red")
            elif isinstance(res, asyncio.CancelledError): console.print(f"Worker {i} cancelled.", style="yellow")
        if res_mon_task: 
            res_mon_task.cancel()
            try: await asyncio.wait_for(res_mon_task, timeout=2.0)
            except (asyncio.TimeoutError, asyncio.CancelledError): pass
            
    generate_html_report(overall_start_time, base_url_schemed, max_depth, excluded_urls_list, req_timeout, ignore_403) # NEW: Pass flag
    generate_csv_log(base_url_schemed)
    final_msg_style = "bold red" if phase_err else "bold green"
    final_msg_suffix = " with errors" if phase_err else "."
    console.print(f"Crawler finished in {format_elapsed_time(time.time() - overall_start_time)}.")
    console.print(f"[FINAL STATUS] Crawler completed{final_msg_suffix}", style=final_msg_style)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Web scraper for broken links.')
    parser.add_argument('url', help='Base URL (e.g., www.example.com or https://example.com)')
    parser.add_argument('--max_depth', type=int, default=DEFAULT_MAX_DEPTH, help=f'Max depth (def: {DEFAULT_MAX_DEPTH})')
    parser.add_argument('--timeout', type=int, default=DEFAULT_TIMEOUT, help=f'Request timeout (def: {DEFAULT_TIMEOUT}s)')
    parser.add_argument('--excluded_urls', nargs='*', default=DEFAULT_EXCLUDED_URLS, help='Full URLs or wildcard domain patterns (e.g., *.example.com) to exclude.')
    parser.add_argument('--verbose', action='store_true', help='Verbose output.')
    parser.add_argument('--sem_limit', type=int, default=SEM_LIMIT, help=f'Concurrent tasks (def: {SEM_LIMIT}).')
    parser.add_argument('--tcp_conn_limit', type=int, default=TCP_CONNECTIONS_LIMIT, help=f'Max TCP connections (def: {TCP_CONNECTIONS_LIMIT}).')
    parser.add_argument('--phase_timeout', type=int, default=ASYNC_PHASE_TIMEOUT, help=f'Phase timeout in sec (def: {ASYNC_PHASE_TIMEOUT}, 0 for none).')
    parser.add_argument('--delay_min', type=float, default=DEFAULT_REQUEST_DELAY_MIN, help=f'Min req delay/worker (def: {DEFAULT_REQUEST_DELAY_MIN}s).')
    parser.add_argument('--delay_max', type=float, default=DEFAULT_REQUEST_DELAY_MAX, help=f'Max req delay/worker (def: {DEFAULT_REQUEST_DELAY_MAX}s). Set to 0 for no artificial delay.')
    parser.add_argument('--ignore-403', action='store_true', help='Ignore 403 Forbidden errors in the final report.') # NEW: command-line flag

    args = parser.parse_args()

    SEM_LIMIT = args.sem_limit; TCP_CONNECTIONS_LIMIT = args.tcp_conn_limit
    ASYNC_PHASE_TIMEOUT = args.phase_timeout; DEFAULT_TIMEOUT = args.timeout
        
    try:
        asyncio.run(main_crawler(
            args.url, args.max_depth, args.excluded_urls, args.verbose, 
            args.timeout, args.delay_min, args.delay_max, args.ignore_403 # NEW: Pass flag
        ))
    except KeyboardInterrupt: console.print("\n[INTERRUPTED] Crawler shut down by user.", style="bold yellow")
    except Exception as e:
        console.print(f"\n[FATAL] An unexpected error occurred in main execution: {type(e).__name__} - {e}", style="bold red")
        import traceback; traceback.print_exc()
