# -*- coding: utf-8 -*-
"""GXGC 管线数据库可视化与撞管分析系统 v2.2
功能：SHP 读取 / 2D-3D 图形浏览 / 管线段·管线点查表 / 管长统计
      撞管检测（平面+立面，结果表停靠于平面图下方同屏查看）/
      纵断面图（单段 / 拉框多段串接） / DXF 导出（国标字体+风险点标记）/
      SHP 导出 / 撞管检测报告(HTML) / 撞管结果导出(CSV) / 统计报表(HTML) / 长度汇总表(HTML)
      新增：最近文件夹记忆、按管线类型显隐图层、按点号/GID 定位
"""
import os
import sys
import json
import math
import datetime
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

import shapefile

VERSION = "2.2"

CONFIG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".gxviewer_cfg.json")


def load_cfg():
    try:
        with open(CONFIG_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_cfg(cfg):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

TYPE_COLOR = {"YS": "#e74c3c", "WS": "#8e44ad", "JS": "#2980b9", "RQ": "#e67e22",
              "DL": "#f1c40f", "TX": "#16a085", "RM": "#7f8c8d"}
TYPE_NAME = {"YS": "雨水", "WS": "污水", "JS": "给水", "RQ": "燃气",
             "DL": "电力", "TX": "通信", "RM": "热力"}
TYPE_ACI = {"YS": 1, "WS": 6, "JS": 5, "RQ": 30, "DL": 2, "TX": 4, "RM": 8}
KIND_TXT = {"clash": "撞管", "warn": "净距不足", "ok": "正常", "unknown": "缺高程"}


def _f(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


class Line:
    __slots__ = ("gid", "type", "dia", "pts", "st", "ed", "sdeep", "edeep", "attrs")
    def __init__(self, **kw):
        for k in self.__slots__:
            setattr(self, k, kw.get(k))


class Pt:
    __slots__ = ("gid", "type", "name", "x", "y", "ground_h", "bottom_h", "source", "attrs")
    def __init__(self, **kw):
        for k in self.__slots__:
            setattr(self, k, kw.get(k))


# ═════════════ 数据读取 ═════════════

def load_shp_folder(folder):
    lines, points = [], []
    schemas = {}     # "L"/"P" → pyshp 字段定义（含字段名，供导出还原结构）
    prj_txt = ""     # 坐标系定义（.prj），导出时回写
    for fn in sorted(os.listdir(folder)):
        if not fn.lower().endswith(".shp"):
            continue
        path = os.path.join(folder, fn)
        try:
            r = shapefile.Reader(path, encoding="gbk")
        except Exception:
            try:
                r = shapefile.Reader(path, encoding="utf-8")
            except Exception:
                continue
        key = "L" if fn.upper().endswith("L.SHP") else "P"
        try:
            schemas[key] = list(r.fields)
            fields = [f[0] for f in r.fields[1:]]
            for s, rec in zip(r.shapes(), r.records()):
                d = dict(zip(fields, list(rec)))
                if fn.upper().endswith("L.SHP"):
                    lines.append(Line(
                        gid=str(d.get("GID", "")).upper(),
                        type=str(d.get("Type", "")).strip(),
                        dia=_f(d.get("Height")) or 0,
                        pts=[(p[1], p[0]) for p in s.points],   # (东,北)→(北,东)
                        st=str(d.get("StGlobalID", "")).upper(),
                        ed=str(d.get("EdGlobalID", "")).upper(),
                        sdeep=_f(d.get("StartDeep")) or 0,
                        edeep=_f(d.get("EndDeep")) or 0,
                        attrs=d))
                else:
                    points.append(Pt(
                        gid=str(d.get("GID", d.get("GlobalID", "")) or "").upper(),
                        type=str(d.get("Type", "")).strip(),
                        name=str(d.get("Exp_No", d.get("点号", "")) or "").strip(),
                        x=_f(d.get("X")), y=_f(d.get("Y")),
                        ground_h=_f(d.get("GroundH")),
                        bottom_h=_f(d.get("BottomH")),
                        source=str(d.get("PtSource", "1")).strip(),
                        attrs=d))
        finally:
            r.close()
    for fn in sorted(os.listdir(folder)):
        if fn.lower().endswith(".prj"):
            try:
                with open(os.path.join(folder, fn), "r",
                          encoding="utf-8", errors="ignore") as f:
                    prj_txt = f.read().strip()
            except Exception:
                pass
            break
    return lines, points, schemas, prj_txt


# ═════════════ 几何与撞管 ═════════════

def seg_int(p1, p2, p3, p4):
    x1, y1 = p1; x2, y2 = p2; x3, y3 = p3; x4, y4 = p4
    den = (x2 - x1) * (y4 - y3) - (y2 - y1) * (x4 - x3)
    if abs(den) < 1e-12:
        return None
    t = ((x3 - x1) * (y4 - y3) - (y3 - y1) * (x4 - x3)) / den
    u = ((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) / den
    if 0 <= t <= 1 and 0 <= u <= 1:
        return t, u
    return None


def line_ends_bottom(line, pt_map):
    """起终点 (管底标高, 地面高程)"""
    def end(gid, deep):
        p = pt_map.get(gid)
        if p and p.ground_h is not None:
            return p.ground_h - deep, p.ground_h
        return None, None
    b0, g0 = end(line.st, line.sdeep)
    b1, g1 = end(line.ed, line.edeep)
    return (b0, b1), (g0, g1)


def interp_ends(v0, v1, t):
    if v0 is None and v1 is None:
        return None
    if v0 is None:
        return v1
    if v1 is None:
        return v0
    return v0 + (v1 - v0) * t


def seg_lens(pts):
    return [math.dist(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]


def clash_detect(lines, points, warn_gap=0.3):
    """撞管检测：排除窨井内交汇，交叉点做立面净距分析"""
    pt_map = {p.gid: p for p in points if p.gid}
    bottom_cache = {ln.gid: line_ends_bottom(ln, pt_map) for ln in lines}
    results = []

    def share_node(a, b):
        return (a.st and a.st in (b.st, b.ed)) or (a.ed and a.ed in (b.st, b.ed))

    n = len(lines)
    for i in range(n):
        a = lines[i]
        (ab0, ab1), _ = bottom_cache[a.gid]
        for j in range(i + 1, n):
            b = lines[j]
            if share_node(a, b):
                continue
            (bb0, bb1), _ = bottom_cache[b.gid]
            for k in range(len(a.pts) - 1):
                for m in range(len(b.pts) - 1):
                    r = seg_int(a.pts[k], a.pts[k + 1], b.pts[m], b.pts[m + 1])
                    if not r:
                        continue
                    ta, ua = r
                    eps = 0.003
                    if ta < eps or ta > 1 - eps or ua < eps or ua > 1 - eps:
                        continue
                    sa, sb = seg_lens(a.pts), seg_lens(b.pts)
                    t_a = (sum(sa[:k]) + ta * sa[k]) / (sum(sa) or 1)
                    t_b = (sum(sb[:m]) + ua * sb[m]) / (sum(sb) or 1)
                    b1 = interp_ends(ab0, ab1, t_a)
                    b2 = interp_ends(bb0, bb1, t_b)
                    pos = (a.pts[k][0] + (a.pts[k + 1][0] - a.pts[k][0]) * ta,
                           a.pts[k][1] + (a.pts[k + 1][1] - a.pts[k][1]) * ta)
                    if b1 is None or b2 is None:
                        results.append({"l1": a, "l2": b, "pos": pos, "b1": b1, "b2": b2,
                                        "t1": None, "t2": None, "gap": None,
                                        "kind": "unknown"})
                        continue
                    d1, d2 = (a.dia or 0) / 1000.0, (b.dia or 0) / 1000.0
                    t1, t2 = b1 + d1, b2 + d2
                    if b1 < t2 - 1e-9 and b2 < t1 - 1e-9:
                        kind, gap = "clash", -(min(t1, t2) - max(b1, b2))
                    else:
                        gap = max(b1, b2) - min(t1, t2)
                        kind = "warn" if gap < warn_gap else "ok"
                    results.append({"l1": a, "l2": b, "pos": pos, "b1": b1, "b2": b2,
                                    "t1": t1, "t2": t2, "gap": gap, "kind": kind})
    return results


# ═════════════ 统计 ═════════════

def compute_stats(lines):
    agg = {}
    for ln in lines:
        L = sum(seg_lens(ln.pts))
        key = (ln.type, ln.dia)
        cnt, tot = agg.get(key, (0, 0.0))
        agg[key] = (cnt + 1, tot + L)
    total = sum(v[1] for v in agg.values())
    rows = []
    for (t, dia), (cnt, L) in sorted(agg.items(), key=lambda kv: (kv[0][0], -kv[0][1])):
        rows.append({"type": t, "dia": dia, "count": cnt, "len": L,
                     "pct": (L / total * 100) if total else 0})
    return rows, total


def stats_conclusion(lines, rows, total):
    if not rows:
        return "数据库为空。"
    by_type = {}
    for r in rows:
        t = by_type.setdefault(r["type"], {"n": 0, "len": 0.0, "dias": []})
        t["n"] += r["count"]; t["len"] += r["len"]; t["dias"].append(r["dia"])
    depths = [d for ln in lines for d in (ln.sdeep, ln.edeep) if d]
    parts = [f"数据库共包含管线段 {len(lines)} 条，总长度 {total:.1f} m。"]
    for t, v in sorted(by_type.items()):
        dias = sorted(v["dias"])
        dr = f"Φ{dias[0]:g}" if dias[0] == dias[-1] else f"Φ{dias[0]:g}~Φ{dias[-1]:g}"
        parts.append(f"其中{TYPE_NAME.get(t, t)}管 {v['n']} 段共 {v['len']:.1f} m"
                     f"（占 {v['len'] / total * 100:.1f}%），管径 {dr}；")
    if depths:
        parts.append(f"管道埋深范围 {min(depths):.2f} ~ {max(depths):.2f} m。")
    big = max(rows, key=lambda r: r["len"])
    parts.append(f"最大单项为{TYPE_NAME.get(big['type'], big['type'])} Φ{big['dia']:g}，"
                 f"共 {big['len']:.1f} m，占管线总长的 {big['pct']:.1f}%。")
    return "".join(parts)


def compute_summary(lines, points):
    """汇总长度表（两列：统计类型 / 统计结果），行序同汇总报表惯例"""
    rows, total = compute_stats(lines)
    out = [("管点个数总计", f"{len(points)}")]
    by_type = {}
    for r in rows:
        by_type[r["type"]] = by_type.get(r["type"], 0.0) + r["len"]
    for t, L in sorted(by_type.items(), key=lambda kv: -kv[1]):
        out.append((TYPE_NAME.get(t, t), f"{L:.2f}米"))
    out.append(("管线长度总计", f"{total:.2f}米"))
    out.append(("管线段数总计", f"{len(lines)}"))
    for r in rows:
        out.append((f"{TYPE_NAME.get(r['type'], r['type'])}-管径: {r['dia']:g}",
                    f"{r['len']:.2f}米"))
    return out


# ═════════════ DXF 导出 ═════════════

def export_dxf(lines, points, clashes, path):
    """R12 ASCII DXF：管线按类别分层，风险点红色圆圈+十字+文字标记
    文字样式为国标字体：gbenor.shx + 长仿宋体 gbcbig.shx"""
    def LAYER(name, color):
        return ["0", "LAYER", "2", name, "70", "0", "62", str(color), "6", "CONTINUOUS"]
    def LINE(lay, x1, y1, x2, y2):
        return ["0", "LINE", "8", lay,
                "10", f"{x1:.3f}", "20", f"{y1:.3f}", "30", "0.0",
                "11", f"{x2:.3f}", "21", f"{y2:.3f}", "31", "0.0"]
    def CIRCLE(lay, x, y, r):
        return ["0", "CIRCLE", "8", lay, "10", f"{x:.3f}", "20", f"{y:.3f}",
                "30", "0.0", "40", f"{r:.3f}"]
    def TEXT(lay, x, y, h, s):
        return ["0", "TEXT", "8", lay, "7", "GB", "10", f"{x:.3f}", "20", f"{y:.3f}",
                "30", "0.0", "40", f"{h:.3f}", "1", s]

    layers = {}
    for ln in lines:
        layers.setdefault(TYPE_NAME.get(ln.type, ln.type), TYPE_ACI.get(ln.type, 7))
    layers["管线点"] = 7
    layers["标注"] = 7
    layers["风险点标记"] = 1

    out = ["0", "SECTION", "2", "HEADER", "9", "$ACADVER", "1", "AC1009",
           "0", "ENDSEC",
           "0", "SECTION", "2", "TABLES", "0", "TABLE", "2", "LAYER",
           "70", str(len(layers))]
    for name, color in layers.items():
        out += LAYER(name, color)
    # 文字样式表：国标字体（直体 gbenor.shx + 中文长仿宋 gbcbig.shx）
    out += ["0", "ENDTAB",
            "0", "TABLE", "2", "STYLE", "70", "1",
            "0", "STYLE", "2", "GB", "70", "0",
            "40", "0.0", "41", "0.8", "50", "0.0", "71", "0",
            "42", "2.5", "3", "gbenor.shx", "4", "gbcbig.shx",
            "0", "ENDTAB",
            "0", "ENDSEC", "0", "SECTION", "2", "ENTITIES"]

    for ln in lines:      # DXF: x=东, y=北
        lay = TYPE_NAME.get(ln.type, ln.type)
        for i in range(len(ln.pts) - 1):
            out += LINE(lay, ln.pts[i][1], ln.pts[i][0],
                        ln.pts[i + 1][1], ln.pts[i + 1][0])
    for p in points:
        if p.x is None:
            continue
        out += CIRCLE("管线点", p.y, p.x, 0.25)
        if p.name:
            out += TEXT("标注", p.y, p.x + 0.4, 1.0, p.name)
    for c in clashes:
        if c["kind"] == "ok":
            continue
        x, y = c["pos"][1], c["pos"][0]      # 东, 北
        color_tag = "撞管" if c["kind"] == "clash" else "净距不足"
        out += CIRCLE("风险点标记", x, y, 0.8)
        out += LINE("风险点标记", x - 1.0, y, x + 1.0, y)
        out += LINE("风险点标记", x, y - 1.0, x, y + 1.0)
        gap = f"{c['gap']:+.2f}m" if c["gap"] is not None else "?"
        a, b = c["l1"], c["l2"]
        out += TEXT("风险点标记", x + 1.2, y, 0.9,
                    f"{color_tag}:{a.type}{a.dia:g}/{b.type}{b.dia:g} 净距{gap}")
    out += ["0", "ENDSEC", "0", "EOF"]
    with open(path, "w", encoding="gbk", errors="replace") as f:
        f.write("\n".join(out))
    return path


# ═════════════ SHP 导出 ═════════════

def export_shp(lines, points, schemas, prj_txt, folder):
    """按入库原始字段结构导出：管线L.shp(折线) + 管点P.shp(点)，并回写 .prj"""
    os.makedirs(folder, exist_ok=True)

    def _write(path, key, shp_type, items):
        w = shapefile.Writer(target=path, shapeType=shp_type, encoding="gbk")
        spec = []
        for f in schemas.get(key, [])[1:]:
            name, ftype = f[0], f[1]
            size = f[2] if len(f) > 2 and f[2] else (50 if ftype == "C" else 18)
            dec = f[3] if len(f) > 3 and f[3] else 0
            try:
                w.field(name, ftype, size, dec)
            except Exception:
                w.field(name, "C", 50)
            spec.append((name, ftype))
        for draw, rec in items:
            draw(w)
            vals = []
            for name, ftype in spec:
                v = rec.get(name)
                if v is None or v == "":
                    v = 0 if ftype in ("N", "F") else ""
                vals.append(v)
            w.record(*vals)
        w.close()

    _write(os.path.join(folder, "管线L.shp"), "L", shapefile.POLYLINE,
           [(lambda w, pts=[(p[1], p[0]) for p in ln.pts]:
             w.line([pts]), ln.attrs) for ln in lines])
    _write(os.path.join(folder, "管点P.shp"), "P", shapefile.POINT,
           [(lambda w, x=p.y, y=p.x: w.point(x, y), p.attrs)
            for p in points if p.x is not None])
    if prj_txt:
        for fn in ("管线L.prj", "管点P.prj"):
            with open(os.path.join(folder, fn), "w", encoding="utf-8") as f:
                f.write(prj_txt)
    return folder


# ═════════════ HTML 报告 ═════════════

CSS = """:root{--ink:#1a2433;--line:#d8dee8;--a:#c0392b;--b:#d35400;--ok:#1e8449;--blue:#1f5fa8}
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:"Microsoft YaHei",SimSun,serif;color:var(--ink);line-height:1.7;font-size:14px;
  background:#f4f6fa}.page{max-width:960px;margin:0 auto;padding:28px 34px;background:#fff;
  box-shadow:0 0 14px rgba(0,0,0,.06)}
h1{font-size:22px;text-align:center;letter-spacing:.3em;margin:6px 0 2px}
.sub{text-align:center;color:#5a6678;font-size:13px;margin-bottom:16px}
.band{display:flex;justify-content:space-between;border-top:3px solid var(--ink);
  border-bottom:1px solid var(--line);padding:8px 2px;margin-bottom:18px;font-size:13px;color:#5a6678;flex-wrap:wrap}
h2{font-size:16px;border-left:5px solid var(--blue);padding-left:10px;margin:24px 0 10px;
  background:linear-gradient(90deg,#eef4fb,transparent)}
table{width:100%;border-collapse:collapse;margin:8px 0 14px;font-size:13px}
th,td{border:1px solid var(--line);padding:6px 9px;text-align:left}
th{background:#eef2f8;font-weight:600}tr:nth-child(even) td{background:#fafbfd}
.tag{display:inline-block;padding:1px 9px;border-radius:3px;color:#fff;font-size:12px;font-weight:600}
.tA{background:var(--a)}.tB{background:var(--b)}.tOk{background:var(--ok)}
.num{font-family:Consolas,monospace}.foot{margin-top:30px;border-top:1px solid var(--line);
  padding-top:12px;font-size:12.5px;color:#5a6678}
.warn{border:2px solid var(--a);padding:14px 18px;margin:14px 0;background:#fdf6f5}"""


def _e(s):
    return str(s if s is not None else "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _meta(lines):
    road = proj = owner = ""
    for ln in lines:
        road = ln.attrs.get("RoadName", "") or road
        proj = ln.attrs.get("Project", "") or proj
        owner = ln.attrs.get("Owner", "") or owner
        if road and proj:
            break
    return road, proj, owner


def build_clash_html(lines, points, clashes, path):
    road, proj, owner = _meta(lines)
    rows, total = compute_stats(lines)
    n_clash = [c for c in clashes if c["kind"] == "clash"]
    n_warn = [c for c in clashes if c["kind"] == "warn"]
    n_unk = [c for c in clashes if c["kind"] == "unknown"]

    h = ['<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8">',
         '<title>管线撞管检测报告</title>', f'<style>{CSS}</style></head><body><div class="page">',
         '<h1>管线撞管检测报告</h1>',
         f'<div class="sub">{_e(proj or "管线数据库")} · 自动化立面净距分析</div>',
         '<div class="band">',
         f'<span>所属道路：{_e(road or "-")}</span><span>权属：{_e(owner or "-")}</span>',
         f'<span>检测日期：{datetime.date.today().isoformat()}</span></div>']

    h.append('<h2>一、检测概况</h2><table>')
    h.append(f'<tr><th>管线段</th><td class="num">{len(lines)} 条</td>'
             f'<th>管线点</th><td class="num">{len(points)} 个</td>'
             f'<th>管线总长</th><td class="num">{total:.1f} m</td></tr>')
    h.append(f'<tr><th>交叉检测点</th><td class="num">{len(clashes)} 处</td>'
             f'<th>撞管（立面重叠）</th><td><b style="color:#c0392b">{len(n_clash)} 处</b></td>'
             f'<th>净距不足</th><td><b style="color:#d35400">{len(n_warn)} 处</b></td></tr></table>')

    h.append('<h2>二、结论</h2>')
    if n_clash:
        h.append(f'<div class="warn"><b>检出 {len(n_clash)} 处撞管（立面重叠）</b>，'
                 f'{len(n_warn)} 处净距不足。撞管位置建议现场开挖核实或复核测量数据；'
                 f'净距不足位置应结合相关规范（一般管线间垂直净距≥0.15m）评估是否需要保护措施。</div>')
    elif n_warn:
        h.append(f'<div class="warn"><b>未检出立面重叠，但存在 {len(n_warn)} 处净距不足</b>，'
                 f'建议结合规范复核最小垂直净距要求，必要时现场核实。</div>')
    elif clashes:
        h.append('<p><b>全部交叉点立面净距满足要求。</b></p>')
    else:
        h.append('<p>未发现管线平面交叉（窨井内交汇属正常连接，不参与判定）。</p>')

    h.append('<h2>三、交叉点明细</h2>')
    if clashes:
        h.append('<table><tr><th>序号</th><th>判定</th><th>管线①</th><th>管底①</th>'
                 '<th>管线②</th><th>管底②</th><th>垂直净距(m)</th><th>位置(东,北)</th></tr>')
        for i, c in enumerate(clashes, 1):
            a, b = c["l1"], c["l2"]
            tag = {"clash": '<span class="tag tA">撞管</span>',
                   "warn": '<span class="tag tB">净距不足</span>',
                   "ok": '<span class="tag tOk">正常</span>',
                   "unknown": "缺高程"}[c["kind"]]
            gap = f'{c["gap"]:+.3f}' if c["gap"] is not None else "-"
            b1 = f'{c["b1"]:.3f}' if c["b1"] is not None else "-"
            b2 = f'{c["b2"]:.3f}' if c["b2"] is not None else "-"
            h.append(f'<tr><td class="num">{i}</td><td>{tag}</td>'
                     f'<td>{TYPE_NAME.get(a.type, a.type)} Φ{a.dia:g}</td><td class="num">{b1}</td>'
                     f'<td>{TYPE_NAME.get(b.type, b.type)} Φ{b.dia:g}</td><td class="num">{b2}</td>'
                     f'<td class="num">{gap}</td><td class="num">{c["pos"][1]:.2f}, {c["pos"][0]:.2f}</td></tr>')
        h.append('</table>')
    else:
        h.append('<p>（无交叉点）</p>')

    h.append('<h2>四、管长统计</h2><table>'
             '<tr><th>类别</th><th>管径(mm)</th><th>段数</th><th>长度(m)</th><th>占比</th></tr>')
    for r in rows:
        h.append(f'<tr><td>{TYPE_NAME.get(r["type"], r["type"])}</td><td class="num">{r["dia"]:g}</td>'
                 f'<td class="num">{r["count"]}</td><td class="num">{r["len"]:.1f}</td>'
                 f'<td class="num">{r["pct"]:.1f}%</td></tr>')
    h.append(f'<tr><th colspan="3">合计</th><th class="num">{total:.1f}</th><th>100%</th></tr></table>')

    h.append(f'<div class="foot">检测方法：管线平面求交（窨井内共享节点交汇视为正常连接）→ '
             f'交叉点按起终点"地面高程−埋深"线性内插管底标高，管顶=管底+管径，立面区间分析。'
             f'<br>管底标高为内插概略值（未计坡度折点与壁厚），判定结果供排查参考，'
             f'精确结论以实测断面为准。DXF 图形（含风险点标记）可由系统同步导出。<br>'
             f'生成时间：{datetime.datetime.now():%Y-%m-%d %H:%M:%S} · '
             f'管线数据库可视化与撞管分析系统 v2.1</div>')
    h.append('</div></body></html>')
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(h))
    return path


def build_stats_html(lines, rows, total, path):
    road, proj, owner = _meta(lines)
    con = stats_conclusion(lines, rows, total)
    h = ['<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8">',
         '<title>管线长度统计报表</title>', f'<style>{CSS}</style></head><body><div class="page">',
         '<h1>管线长度统计报表</h1>',
         f'<div class="sub">{_e(proj or "管线数据库")}</div>',
         '<div class="band">',
         f'<span>所属道路：{_e(road or "-")}</span>',
         f'<span>生成日期：{datetime.date.today().isoformat()}</span></div>',
         '<h2>一、统计结论</h2>',
         f'<p style="background:#f7fafd;padding:12px 16px;border-left:4px solid #1f5fa8">{_e(con)}</p>',
         '<h2>二、分项统计</h2><table>'
         '<tr><th>类别</th><th>管径(mm)</th><th>段数</th><th>长度(m)</th><th>占比</th></tr>']
    for r in rows:
        h.append(f'<tr><td>{TYPE_NAME.get(r["type"], r["type"])}</td><td class="num">{r["dia"]:g}</td>'
                 f'<td class="num">{r["count"]}</td><td class="num">{r["len"]:.1f}</td>'
                 f'<td class="num">{r["pct"]:.1f}%</td></tr>')
    h.append(f'<tr><th colspan="3">合计</th><th class="num">{total:.1f}</th><th>100%</th></tr></table>')
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(h))
    return path


def build_summary_html(lines, points, path):
    """汇总长度表 HTML（与界面"长度表"页同格式）"""
    road, proj, owner = _meta(lines)
    rows_sum = compute_summary(lines, points)
    rows, total = compute_stats(lines)
    h = ['<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8">',
         '<title>管线长度汇总表</title>', f'<style>{CSS}</style></head><body><div class="page">',
         '<h1>管线长度汇总表</h1>',
         f'<div class="sub">{_e(proj or "管线数据库")}</div>',
         '<div class="band">',
         f'<span>所属道路：{_e(road or "-")}</span>',
         f'<span>生成日期：{datetime.date.today().isoformat()}</span></div>',
         '<table><tr><th style="width:55%">统计类型</th><th>统计结果</th></tr>']
    for k, v in rows_sum:
        h.append(f'<tr><td>{_e(k)}</td><td class="num" style="text-align:right">{_e(v)}</td></tr>')
    h.append('</table>')
    h.append('<h2>分类明细</h2><table>'
             '<tr><th>类别</th><th>管径(mm)</th><th>段数</th><th>长度(m)</th><th>占比</th></tr>')
    for r in rows:
        h.append(f'<tr><td>{TYPE_NAME.get(r["type"], r["type"])}</td><td class="num">{r["dia"]:g}</td>'
                 f'<td class="num">{r["count"]}</td><td class="num">{r["len"]:.1f}</td>'
                 f'<td class="num">{r["pct"]:.1f}%</td></tr>')
    h.append(f'<tr><th colspan="3">合计</th><th class="num">{total:.1f}</th><th>100%</th></tr></table>')
    h.append(f'<div class="foot">统计口径：按管线属性（类别 Type、管径 Height）汇总几何长度，'
             f'管点个数按管点表记录数统计。'
             f'<br>生成时间：{datetime.datetime.now():%Y-%m-%d %H:%M:%S} · '
             f'管线数据库可视化与撞管分析系统 v2.1</div></div></body></html>')
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(h))
    return path


# ═════════════ 纵断面窗口 ═════════════

def chain_tracks(lines):
    """把选中的管线按共享节点串接成若干条路径（可折线连续）。
    返回 track 列表，每个 track = [(line, rev), ...]（rev=该段是否反向）"""
    unused = list(lines)
    tracks = []

    def tail_end(t):
        ln, rev = t
        return ln.st if rev else ln.ed

    def head_end(t):
        ln, rev = t
        return ln.ed if rev else ln.st

    while unused:
        a = unused.pop(0)
        track = [(a, False)]
        while True:                      # 向下游延伸
            fe = tail_end(track[-1])
            k = next((k for k, u in enumerate(unused)
                      if u.st == fe or u.ed == fe), None)
            if k is None:
                break
            u = unused.pop(k)
            track.append((u, u.st != fe))
        while True:                      # 向上游延伸
            fh = head_end(track[0])
            k = next((k for k, u in enumerate(unused)
                      if u.st == fh or u.ed == fh), None)
            if k is None:
                break
            u = unused.pop(k)
            track.insert(0, (u, u.ed != fh))
        tracks.append(track)
    return tracks


def track_data(track, pt_map):
    """路径 → (里程列表, 地面高程列表, 管底高程列表)"""
    ds, gs, bs = [], [], []
    d = 0.0
    for ln, rev in track:
        sp, ep = pt_map.get(ln.st), pt_map.get(ln.ed)
        g0 = sp.ground_h if sp and sp.ground_h is not None else None
        g1 = ep.ground_h if ep and ep.ground_h is not None else None
        b0 = (g0 - ln.sdeep) if g0 is not None else None
        b1 = (g1 - ln.edeep) if g1 is not None else None
        if rev:
            g0, g1, b0, b1 = g1, g0, b1, b0
        vpts = ln.pts[::-1] if rev else ln.pts
        lens = seg_lens(vpts)
        total_l = sum(lens) or 1
        acc = 0.0
        for i, p in enumerate(vpts):
            if ds and i == 0:            # 路径内部节点只取一次
                acc += lens[0] if lens else 0.0
                continue
            ds.append(d + acc)
            gs.append(interp_ends(g0, g1, acc / total_l))
            bs.append(interp_ends(b0, b1, acc / total_l))
            acc += lens[i] if i < len(lens) else 0.0
        d += total_l
    return ds, gs, bs


class ProfileWin(tk.Toplevel):
    def __init__(self, master, tracks, sel_lines, pt_map, font_size=9):
        """tracks: chain_tracks 产出的路径列表（单段管线即单路径单段）"""
        super().__init__(master)
        n = len(tracks)
        m = len(sel_lines)
        if n == 1:
            t = tracks[0][0][0]
            sp, ep = pt_map.get(t.st), pt_map.get(t.ed)
            self.title(f"纵断面 — {TYPE_NAME.get(t.type, t.type)} Φ{t.dia:g}  "
                       f"({sp.name if sp and sp.name else '?'}→{ep.name if ep and ep.name else '?'})"
                       + (f"  共{m}段" if m > 1 else ""))
        else:
            self.title(f"纵断面 — 框选 {m} 段串成 {n} 条路径（分页查看）")
        self.geometry("980x480")
        self.pt_map = pt_map
        self.fs = font_size
        self.tracks = tracks
        if n == 1:
            cv = tk.Canvas(self, bg="white")
            cv.pack(fill="both", expand=True, padx=6, pady=6)
            cv.bind("<Configure>", lambda e: self._draw(cv, tracks[0]))
            self.after(60, lambda: self._draw(cv, tracks[0]))
        else:
            nb = ttk.Notebook(self)
            nb.pack(fill="both", expand=True, padx=6, pady=6)
            for k, tr in enumerate(tracks, 1):
                fr = ttk.Frame(nb)
                nb.add(fr, text=f" 路径{k}（{len(tr)}段 "
                                f"{sum(sum(seg_lens(p.pts)) for p, _ in tr):.1f}m） ")
                cv = tk.Canvas(fr, bg="white")
                cv.pack(fill="both", expand=True)
                cv.bind("<Configure>", lambda e, c=cv, t=tr: self._draw(c, t))
                self.after(60, lambda c=cv, t=tr: self._draw(c, t))

    def _draw(self, cv, track):
        cv.delete("all")
        fs = self.fs
        cv.update_idletasks()
        W, H = cv.winfo_width(), cv.winfo_height()
        if W < 50:
            W, H = 960, 420
        ml, mr, mt, mb = 70, 60, 46, 56
        ds, gs, bs = track_data(track, self.pt_map)
        samples = list(zip(ds, gs, bs))
        total = ds[-1] if ds else 0
        vals = [v for _, g, b in samples for v in (g, b) if v is not None]
        if not vals:
            cv.create_text(W / 2, H / 2, text="所选管线缺少端点地面高程，无法绘制纵断面",
                           fill="#999", font=("", 12))
            return
        vmin, vmax = min(vals), max(vals)
        pad = max(0.5, (vmax - vmin) * 0.15)
        vmin, vmax = vmin - pad, vmax + pad

        def X(d):
            return ml + d / (total or 1) * (W - ml - mr)

        def Y(v):
            return H - mb - (v - vmin) / (vmax - vmin) * (H - mt - mb)

        for k in range(6):
            v = vmin + (vmax - vmin) * k / 5
            y = Y(v)
            cv.create_line(ml, y, W - mr, y, fill="#e3e8ef")
            cv.create_text(ml - 6, y, text=f"{v:.2f}", anchor="e",
                           font=("", max(6, fs - 2)), fill="#666")
        for k in range(6):
            d = total * k / 5
            x = X(d)
            cv.create_line(x, mt, x, H - mb, fill="#eef1f6")
            cv.create_text(x, H - mb + 8, text=f"{d:.1f}",
                           font=("", max(6, fs - 2)), fill="#666")
        cv.create_text(W / 2, H - 14, text="里程 (m)", font=("", fs))
        cv.create_text(16, H / 2, text="标高 (m)", font=("", fs))

        def poly(idx):
            return [c for s in samples if s[idx] is not None for c in (X(s[0]), Y(s[idx]))]

        if samples[0][1] is not None and samples[0][2] is not None:
            fill = []
            for s in samples:
                fill += [X(s[0]), Y(s[1])]
            for s in reversed(samples):
                fill += [X(s[0]), Y(s[2])]
            if len(fill) >= 6:
                cv.create_polygon(*fill, fill="#fdecea", outline="")
        if len(poly(1)) >= 4:
            cv.create_line(*poly(1), fill="#27ae60", width=2)
        if len(poly(2)) >= 4:
            cv.create_line(*poly(2), fill="#c0392b", width=4)
        for s in samples:
            if s[1] is not None:
                cv.create_text(X(s[0]), Y(s[1]) - 8, text=f"{s[1]:.2f}",
                               font=("", max(6, fs - 2)), fill="#27ae60")
            if s[2] is not None:
                cv.create_text(X(s[0]), Y(s[2]) + 10, text=f"{s[2]:.2f}",
                               font=("", max(6, fs - 2)), fill="#c0392b")
        cv.create_text(W / 2, 12, font=("", fs),
                       text=f"纵断面  绿=地面线  红=管底线   全长 {total:.2f} m（{len(track)} 段）")
        if len(track) == 1:
            a = track[0][0]
            if a.sdeep or a.edeep:
                cv.create_text(W / 2, 30, font=("", max(6, fs - 1)), fill="#555",
                               text=f"埋深 {a.sdeep:.2f} ~ {a.edeep:.2f} m")


# ═════════════ 主界面 ═════════════

class App:
    def __init__(self, root):
        self.root = root
        root.title("GXGC 管线数据库可视化与撞管分析系统 v2.2")
        root.geometry("1220x760")
        self.lines, self.points = [], []
        self.pt_map = {}
        self.clashes = []
        self.mode = "2d"
        self.yaw = -0.6
        self.pitch = 0.45
        self.exag = 8.0
        self.scale = 1.0
        self.cx = self.cy = 0.0
        self.drag = None
        self.sel_marks = []
        self.font_size = 8
        self.sel_line = None
        self.box_sel = False       # 拉框选线模式
        self.box_start = None
        self.rect_id = None
        self.schemas = {}
        self.prj_txt = ""
        self.data_dir = ""
        self.cfg = load_cfg()
        self.recent = self.cfg.get("recent", [])
        self.last_dir = self.cfg.get("last_dir", "")
        self.type_hide = set()
        self.type_vars = {}
        self.var_find = tk.StringVar()
        self.show = {"name": tk.BooleanVar(value=True), "dia": tk.BooleanVar(value=True),
                     "bottom": tk.BooleanVar(value=False), "ground": tk.BooleanVar(value=False)}
        self._build()

    # ───── 界面 ─────
    def _build(self):
        # 菜单栏：文件（打开 / 最近 / 退出）、帮助（关于）
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        fmenu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="文件", menu=fmenu)
        fmenu.add_command(label="打开数据文件夹…", command=self.open)
        self.recent_menu = tk.Menu(fmenu, tearoff=0)
        fmenu.add_cascade(label="最近打开", menu=self.recent_menu)
        self._refresh_recent()
        fmenu.add_separator()
        fmenu.add_command(label="退出", command=self.root.quit)
        hmenu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="帮助", menu=hmenu)
        hmenu.add_command(label="关于", command=self._about)
        bar = ttk.Frame(self.root)
        bar.pack(fill="x", padx=6, pady=3)
        ttk.Label(bar, text="QQ：799144685", foreground="#1f5fa8",
                  font=("", 10, "bold")).pack(side="left", padx=(0, 10))
        ttk.Button(bar, text="打开数据文件夹…", command=self.open).pack(side="left")
        self.btn_clash = ttk.Button(bar, text="撞管检测", command=self.do_clash, state="disabled")
        self.btn_clash.pack(side="left", padx=6)
        self.btn_3d = ttk.Button(bar, text="切换 3D", command=self.toggle_3d, state="disabled")
        self.btn_3d.pack(side="left", padx=2)
        ttk.Label(bar, text="净距阈值(m):").pack(side="left", padx=(10, 0))
        self.var_clear = tk.StringVar(value="0.3")
        ttk.Spinbox(bar, from_=0.0, to=2.0, increment=0.05, width=5,
                    textvariable=self.var_clear).pack(side="left", padx=2)
        ttk.Label(bar, text="字号:").pack(side="left", padx=(10, 0))
        self.var_font = tk.StringVar(value="8")
        ttk.Spinbox(bar, from_=5, to=16, increment=1, width=4,
                    textvariable=self.var_font, command=self._font_changed).pack(side="left", padx=2)
        ttk.Label(bar, text="3D竖向夸张:").pack(side="left", padx=(10, 0))
        self.var_exag = tk.StringVar(value="8")
        ttk.Spinbox(bar, from_=1, to=30, increment=1, width=4,
                    textvariable=self.var_exag, command=self._exag_changed).pack(side="left", padx=2)
        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        self.btn_dxf = ttk.Button(bar, text="导出DXF(含风险点)", command=self.exp_dxf, state="disabled")
        self.btn_dxf.pack(side="left")
        self.btn_shp = ttk.Button(bar, text="导出SHP", command=self.exp_shp, state="disabled")
        self.btn_shp.pack(side="left", padx=6)
        self.btn_rep = ttk.Button(bar, text="撞管报告", command=self.exp_clash_rep, state="disabled")
        self.btn_rep.pack(side="left", padx=6)
        self.btn_csv = ttk.Button(bar, text="撞管CSV", command=self.exp_clash_csv, state="disabled")
        self.btn_csv.pack(side="left", padx=2)
        self.var_info = tk.StringVar(value="未加载数据")
        ttk.Label(bar, textvariable=self.var_info).pack(side="right")

        bar2 = ttk.Frame(self.root)
        bar2.pack(fill="x", padx=6)
        ttk.Label(bar2, text="显示：").pack(side="left")
        for key, txt in (("name", "点号"), ("dia", "管径"),
                         ("bottom", "井底标高"), ("ground", "地面高程")):
            ttk.Checkbutton(bar2, text=txt, variable=self.show[key],
                            command=self.redraw).pack(side="left", padx=6)
        ttk.Separator(bar2, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(bar2, text="定位:").pack(side="left")
        ef = ttk.Entry(bar2, textvariable=self.var_find, width=12)
        ef.pack(side="left", padx=2)
        ef.bind("<Return>", lambda e: self._locate())
        ttk.Button(bar2, text="查找", command=self._locate).pack(side="left")
        ttk.Label(bar2, text="（实测点=实心 ●  连接既有井=空心 ○）",
                  foreground="#888").pack(side="left", padx=12)
        self.btn_prof = ttk.Button(bar2, text="纵断面(选中管线)", command=self.show_profile,
                                   state="disabled")
        self.btn_prof.pack(side="left", padx=10)
        self.btn_profbox = ttk.Button(bar2, text="纵断面(拉框多选)", command=self.start_box_profile,
                                      state="disabled")
        self.btn_profbox.pack(side="left")

        main = ttk.PanedWindow(self.root, orient="horizontal")
        main.pack(fill="both", expand=True, padx=6, pady=4)
        left = ttk.Notebook(main)
        main.add(left, weight=3)

        # 图形页：画布 + 底部撞管结果停靠（同屏看平面）
        gfx = ttk.Frame(left)
        left.add(gfx, text=" 图形 ")
        self.canvas = tk.Canvas(gfx, bg="white", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.clash_frame = ttk.Frame(gfx)
        self.tv_clash = ttk.Treeview(self.clash_frame, show="headings", height=6)
        self.tv_clash.pack(fill="both", expand=True)
        self.tv_clash["columns"] = ("idx", "kind", "a", "b", "gap", "pos")
        for col, (txt, w, anc) in {
                "idx": ("序号", 44, "center"), "kind": ("判定", 84, "center"),
                "a": ("管线①", 130, "w"), "b": ("管线②", 130, "w"),
                "gap": ("净距(m)", 80, "center"),
                "pos": ("交叉位置(东,北)", 170, "w")}.items():
            self.tv_clash.heading(col, text=txt)
            self.tv_clash.column(col, width=w, anchor=anc)
        self.tv_clash.bind("<<TreeviewSelect>>", self._clash_pick)

        self.tv_lines = self._make_table(left, " 管线段 ")
        self.tv_points = self._make_table(left, " 管线点 ")

        # 统计页
        stat = ttk.Frame(left)
        left.add(stat, text=" 管长统计 ")
        self.tv_stat = ttk.Treeview(stat, show="headings")
        self.tv_stat.pack(fill="x", pady=4)
        self.tv_stat["columns"] = ("type", "dia", "cnt", "len", "pct")
        for col, (txt, w, anc) in {
                "type": ("类别", 90, "center"), "dia": ("管径(mm)", 100, "center"),
                "cnt": ("段数", 80, "center"), "len": ("长度(m)", 110, "e"),
                "pct": ("占比", 90, "center")}.items():
            self.tv_stat.heading(col, text=txt)
            self.tv_stat.column(col, width=w, anchor=anc)
        self.stat_txt = tk.Text(stat, wrap="word", height=8, font=("", 10))
        self.stat_txt.pack(fill="both", expand=True, pady=4)
        ttk.Button(stat, text="导出统计报表(HTML)", command=self.exp_stats).pack(anchor="e", padx=4)

        # 长度汇总表页（管点个数/分类长度/总计/分类管径长度）
        summ = ttk.Frame(left)
        left.add(summ, text=" 长度表 ")
        self.tv_summ = ttk.Treeview(summ, show="headings")
        self.tv_summ.pack(fill="x", pady=4)
        self.tv_summ["columns"] = ("k", "v")
        self.tv_summ.heading("k", text="统计类型")
        self.tv_summ.column("k", width=280, anchor="w")
        self.tv_summ.heading("v", text="统计结果")
        self.tv_summ.column("v", width=180, anchor="e")
        ttk.Button(summ, text="导出长度表(HTML)",
                   command=self.exp_summary).pack(anchor="e", padx=4, pady=4)

        # 右栏
        right = ttk.Frame(main)
        main.add(right, weight=1)
        ttk.Label(right, text="属性（点击图形要素查看）", font=("", 10, "bold")).pack(anchor="w", pady=4)
        self.attr = tk.Text(right, wrap="word", width=40, font=("Consolas", 9))
        self.attr.pack(fill="both", expand=True)
        legend = ttk.LabelFrame(right, text="图例")
        legend.pack(fill="x", pady=6)
        for t, c in TYPE_COLOR.items():
            f = tk.Frame(legend)
            f.pack(fill="x", padx=6, pady=1)
            tk.Canvas(f, width=22, height=6, bg=c, highlightthickness=0).pack(side="left")
            ttk.Label(f, text=TYPE_NAME.get(t, t)).pack(side="left", padx=6)
        self.type_frame = ttk.LabelFrame(right, text="类型显示（图层显隐）")
        self.type_frame.pack(fill="x", pady=6)
        ttk.Label(self.type_frame, text="勾选=显示；取消=隐藏该类型管线",
                  foreground="#888", font=("", 9)).pack(anchor="w", padx=6)

        self.var_status = tk.StringVar(
            value="就绪 — 打开数据文件夹后：滚轮缩放 / 拖动平移(3D下拖动旋转) / 单击要素看属性")
        ttk.Label(self.root, textvariable=self.var_status, relief="sunken",
                  anchor="w").pack(fill="x", side="bottom")

        self.canvas.bind("<MouseWheel>", self._zoom)
        self.canvas.bind("<ButtonPress-1>", self._press)
        self.canvas.bind("<B1-Motion>", self._drag)
        self.canvas.bind("<ButtonRelease-1>", self._release)
        self.canvas.bind("<Configure>", lambda e: self.redraw())
        self.root.bind("<Escape>", self._cancel_box)

    def _make_table(self, parent, title):
        tv = ttk.Treeview(parent, show="headings")
        tv["columns"] = ("idx", "type", "dia", "name", "x", "y", "gh", "bh", "extra")
        for col, (txt, w, anc) in {
                "idx": ("序号", 44, "center"), "type": ("类别", 46, "center"),
                "dia": ("管径mm", 60, "center"), "name": ("点号/ID", 110, "w"),
                "x": ("纵坐标X", 95, "e"), "y": ("横坐标Y", 95, "e"),
                "gh": ("地面高程", 75, "e"), "bh": ("井底高程", 75, "e"),
                "extra": ("其他", 210, "w")}.items():
            tv.heading(col, text=txt)
            tv.column(col, width=w, anchor=anc)
        parent.add(tv, text=title)
        tv.bind("<<TreeviewSelect>>", self._table_pick)
        return tv

    # ───── 数据 ─────
    def open(self):
        d = filedialog.askdirectory(title="选择含 GXGC 数据(SHP)的文件夹",
                                   initialdir=self.last_dir or None)
        if not d:
            return
        self._load_folder(d)

    def _load_folder(self, d):
        try:
            self.lines, self.points, self.schemas, self.prj_txt = load_shp_folder(d)
        except Exception as e:
            messagebox.showerror("错误", f"读取失败：{e}")
            return
        if not self.lines and not self.points:
            messagebox.showwarning("提示", "该文件夹内未发现 SHP 数据（*.shp）")
            return
        self.data_dir = d
        self.last_dir = d
        if d in self.recent:
            self.recent.remove(d)
        self.recent.insert(0, d)
        self.recent = self.recent[:6]
        save_cfg({"last_dir": self.last_dir, "recent": self.recent})
        self._refresh_recent()
        self.pt_map = {p.gid: p for p in self.points if p.gid}
        for b in (self.btn_clash, self.btn_3d, self.btn_dxf, self.btn_rep,
                  self.btn_profbox, self.btn_shp, self.btn_csv):
            b.config(state="normal")
        self.clashes = []
        self.tv_clash.delete(*self.tv_clash.get_children())
        self.var_info.set(f"管线段 {len(self.lines)} 条 | 管线点 {len(self.points)} 个")
        self.root.title(f"GXGC 可视化 v2.2 — {os.path.basename(d)}")
        self._fill_tables()
        self._fill_stats()
        self._fill_summary()
        self._build_type_filter()
        self._fit()
        self.var_status.set("数据已加载 — 滚轮缩放 / 拖动平移(3D下拖动旋转) / 单击要素看属性 / 菜单「文件>最近打开」可快速重载")

    def _fit(self):
        self.root.update_idletasks()
        xs = [p[0] for ln in self.lines for p in ln.pts] + \
             [p.x for p in self.points if p.x is not None]
        ys = [p[1] for ln in self.lines for p in ln.pts] + \
             [p.y for p in self.points if p.y is not None]
        if not xs:
            return
        self.cx, self.cy = (min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2
        w = max(self.canvas.winfo_width(), 400) - 40
        h = max(self.canvas.winfo_height(), 300) - 40
        self.scale = min(w / ((max(xs) - min(xs)) or 1), h / ((max(ys) - min(ys)) or 1))
        self.redraw()

    # ───── 投影 ─────
    def _to_canvas(self, x, y):
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        return (w / 2 + (y - self.cy) * self.scale,
                h / 2 - (x - self.cx) * self.scale)

    def _proj3d(self, n, e, u):
        """世界(北,东,标高) → 画布坐标；返回 (sx, sy, depth)"""
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        n = n - self.cx
        e = e - self.cy
        a = self.yaw
        u_ax = e * math.cos(a) + n * math.sin(a)
        d_ax = -e * math.sin(a) + n * math.cos(a)
        u_el = u * self.exag
        sy = h / 2 - (u_el * math.cos(self.pitch) + d_ax * math.sin(self.pitch)) * self.scale * 0.9
        sx = w / 2 + u_ax * self.scale
        return sx, sy, d_ax

    # ───── 绘制 ─────
    def redraw(self):
        cv = self.canvas
        cv.delete("all")
        self.sel_marks = []
        if not self.lines and not self.points:
            return
        if self.mode == "3d":
            self._draw_3d(cv)
        else:
            self._draw_2d(cv)

    def _draw_2d(self, cv):
        s = self.scale
        fs = self.font_size
        lw = max(1, min(6, s * 0.3))
        r = max(2, min(8, s * 0.25))
        for c in self.clashes:
            if c["kind"] == "ok":
                continue
            if c["l1"].type in self.type_hide and c["l2"].type in self.type_hide:
                continue
            x, y = self._to_canvas(*c["pos"])
            color = "#c0392b" if c["kind"] == "clash" else "#e67e22"
            cv.create_oval(x - 12, y - 12, x + 12, y + 12, outline=color, width=2)
            cv.create_text(x, y - 16, text=KIND_TXT[c["kind"]], fill=color, font=("", fs))
        for ln in self.lines:
            if ln.type in self.type_hide:
                continue
            color = TYPE_COLOR.get(ln.type, "#34495e")
            pts = []
            for p in ln.pts:
                pts.extend(self._to_canvas(*p))
            if len(pts) >= 4:
                cv.create_line(*pts, fill=color, width=lw, tags=("line", ln.gid))
            if self.show["dia"].get() and ln.dia and s > 2.5:
                mid = ln.pts[len(ln.pts) // 2]
                mx, my = self._to_canvas(*mid)
                cv.create_text(mx, my - 6, text=f"{ln.dia:g}", fill=color, font=("", fs))
        for p in self.points:
            if p.type in self.type_hide:
                continue
            if p.x is None:
                continue
            x, y = self._to_canvas(p.x, p.y)
            fill = TYPE_COLOR.get(p.type, "#555")
            if str(p.source) == "1":
                cv.create_oval(x - r, y - r, x + r, y + r, fill=fill,
                               outline="black", width=0.5, tags=("pt", p.gid))
            else:
                cv.create_oval(x - r, y - r, x + r, y + r, fill="",
                               outline=fill, width=1.5, tags=("pt", p.gid))
            label = None
            if self.show["name"].get() and p.name:
                label = p.name
            elif self.show["bottom"].get() and p.bottom_h is not None:
                label = f"{p.bottom_h:.2f}"
            elif self.show["ground"].get() and p.ground_h is not None:
                label = f"{p.ground_h:.2f}"
            if label and s > 1.0:
                cv.create_text(x, y - r - 4, text=label, fill="#333",
                               font=("", fs), tags=("pt", p.gid))

    def _draw_3d(self, cv):
        fs = self.font_size
        s = self.scale
        lw = max(1, min(5, s * 0.3))
        r = max(2, min(7, s * 0.22))
        prims = []   # (depth, drawfn) 远→近绘制

        xs = [p[0] for ln in self.lines for p in ln.pts]
        ys = [p[1] for ln in self.lines for p in ln.pts]
        if xs:
            x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
            nx = 6
            step_x = (x1 - x0) / nx or 1
            step_y = (y1 - y0) / nx or 1
            ground = 5.0
            grid = []
            for k in range(nx + 1):
                grid.append(((x0 + k * step_x, y0), (x0 + k * step_x, y1)))
                grid.append(((x0, y0 + k * step_y), (x1, y0 + k * step_y)))
            for a, b in grid:
                p1 = self._proj3d(a[0], a[1], ground)
                p2 = self._proj3d(b[0], b[1], ground)
                prims.append((p1[2] + 1e6, lambda p1=p1, p2=p2:
                              cv.create_line(p1[0], p1[1], p2[0], p2[1],
                                             fill="#e3e8ef", width=1)))

        bottom_cache = {ln.gid: line_ends_bottom(ln, self.pt_map) for ln in self.lines}
        for ln in self.lines:
            if ln.type in self.type_hide:
                continue
            (b0, b1), _ = bottom_cache[ln.gid]
            segs = seg_lens(ln.pts)
            total = sum(segs) or 1
            acc = 0
            color = TYPE_COLOR.get(ln.type, "#34495e")
            for i in range(len(ln.pts) - 1):
                t0, t1 = acc / total, (acc + segs[i]) / total
                acc += segs[i]
                u0 = interp_ends(b0, b1, t0)
                u1 = interp_ends(b0, b1, t1)
                if u0 is None:
                    u0 = 0.0
                if u1 is None:
                    u1 = u0
                p1 = self._proj3d(ln.pts[i][0], ln.pts[i][1], u0)
                p2 = self._proj3d(ln.pts[i + 1][0], ln.pts[i + 1][1], u1)
                d = (p1[2] + p2[2]) / 2
                prims.append((d, lambda p1=p1, p2=p2, color=color, lw=lw, gid=ln.gid:
                              cv.create_line(p1[0], p1[1], p2[0], p2[1],
                                             fill=color, width=lw, capstyle="round",
                                             tags=("line", gid))))

        for p in self.points:
            if p.type in self.type_hide:
                continue
            if p.x is None:
                continue
            g = p.ground_h if p.ground_h is not None else 5.0
            btm = p.bottom_h if p.bottom_h is not None else g - 2
            pg = self._proj3d(p.x, p.y, g)
            pb = self._proj3d(p.x, p.y, btm)
            fill = TYPE_COLOR.get(p.type, "#555")
            prims.append((pg[2], lambda pg=pg, pb=pb, fill=fill, r=r, p=p:
                          (cv.create_line(pg[0], pg[1], pb[0], pb[1], fill=fill, width=1),
                           cv.create_oval(pg[0] - r, pg[1] - r, pg[0] + r, pg[1] + r,
                                          fill=fill if str(p.source) == "1" else "",
                                          outline=fill, width=1.2, tags=("pt", p.gid)))))
            if self.show["name"].get() and p.name and s > 1.0:
                prims.append((pg[2], lambda pg=pg, p=p, fs=fs:
                              cv.create_text(pg[0], pg[1] - r - 4, text=p.name,
                                             fill="#333", font=("", fs), tags=("pt", p.gid))))

        for c in self.clashes:
            if c["kind"] == "ok":
                continue
            if c["l1"].type in self.type_hide and c["l2"].type in self.type_hide:
                continue
            el = 0.0
            if c["b1"] is not None or c["b2"] is not None:
                el = min(v for v in (c["b1"], c["b2"]) if v is not None)
            pp = self._proj3d(c["pos"][0], c["pos"][1], el)
            color = "#c0392b" if c["kind"] == "clash" else "#e67e22"
            kind = KIND_TXT[c["kind"]]
            prims.append((pp[2] - 100, lambda pp=pp, color=color, fs=fs, kind=kind:
                          (cv.create_oval(pp[0] - 12, pp[1] - 12, pp[0] + 12, pp[1] + 12,
                                          outline=color, width=2),
                           cv.create_text(pp[0], pp[1] - 16, text=kind,
                                          fill=color, font=("", fs)))))

        for d, fn in sorted(prims, key=lambda t: -t[0]):
            fn()

    # ───── 交互 ─────
    def _zoom(self, e):
        self.scale *= 1.25 if e.delta > 0 else 0.8
        self.redraw()

    def _press(self, e):
        if self.box_sel and self.mode == "2d":
            self.box_start = (e.x, e.y)
            return
        self.drag = (e.x, e.y)

    def _drag(self, e):
        if self.box_sel and self.box_start:
            if self.rect_id:
                self.canvas.delete(self.rect_id)
            self.rect_id = self.canvas.create_rectangle(
                self.box_start[0], self.box_start[1], e.x, e.y,
                outline="#1f5fa8", width=2, dash=(5, 3))
            return
        if not self.drag:
            return
        dx = e.x - self.drag[0]
        dy = e.y - self.drag[1]
        if self.mode == "3d":
            self.yaw += dx * 0.008
            self.pitch = min(1.35, max(0.15, self.pitch + dy * 0.006))
        else:
            # 拖拽方向：内容跟手（向下拖=视野南移=内容下移）
            self.cx += dy / self.scale
            self.cy -= dx / self.scale
        self.drag = (e.x, e.y)
        self.redraw()

    def _release(self, e):
        if self.box_sel and self.box_start:
            x0, y0 = self.box_start
            self.box_start = None
            if self.rect_id:
                self.canvas.delete(self.rect_id)
                self.rect_id = None
            if abs(e.x - x0) >= 5 and abs(e.y - y0) >= 5:
                self._finish_box(x0, y0, e.x, e.y)
            return
        moved = self.drag and (abs(e.x - self.drag[0]) + abs(e.y - self.drag[1]) > 4)
        self.drag = None
        if moved:
            return
        tags = self.canvas.gettags("current")
        if "pt" in tags:
            gid = [t for t in tags if t not in ("pt", "current")]
            if gid:
                self._show_pt(gid[0])
        elif "line" in tags:
            gid = [t for t in tags if t not in ("line", "current")]
            if gid:
                self._show_line(gid[0])
        self.redraw()

    def _font_changed(self):
        try:
            self.font_size = max(5, int(self.var_font.get()))
        except ValueError:
            pass
        self.redraw()

    def _exag_changed(self):
        try:
            self.exag = max(1.0, float(self.var_exag.get()))
        except ValueError:
            pass
        if self.mode == "3d":
            self.redraw()

    def toggle_3d(self):
        self.mode = "3d" if self.mode == "2d" else "2d"
        self.btn_3d.config(text="切换 2D" if self.mode == "3d" else "切换 3D")
        if self.mode == "3d":
            self.scale *= 0.7
        else:
            self.scale /= 0.7
        self.redraw()

    # ───── 属性 ─────
    def _show_attrs(self, d, title):
        self.attr.delete("1.0", "end")
        self.attr.insert("end", f"── {title} ──\n")
        for k, v in d.items():
            if v in ("", None):
                continue
            self.attr.insert("end", f"{k:　<8}: {v}\n")

    def _show_pt(self, gid):
        p = next((q for q in self.points if q.gid == gid), None)
        if not p:
            return
        self._show_attrs(p.attrs, f"管线点 {p.name or gid[:8]}")
        if self.mode == "2d" and p.x is not None:
            x, y = self._to_canvas(p.x, p.y)
            self.sel_marks.append(self.canvas.create_oval(
                x - 14, y - 14, x + 14, y + 14, outline="#2ecc71", width=3))
        self.var_status.set(f"管线点 {p.name or gid[:8]}：X={p.x} Y={p.y} "
                            f"地面={p.ground_h} 井底={p.bottom_h}")

    def _show_line(self, gid):
        ln = next((q for q in self.lines if q.gid == gid), None)
        if not ln:
            return
        self.sel_line = ln
        self.btn_prof.config(state="normal")
        self._show_attrs(ln.attrs, f"管线段 {ln.type} Φ{ln.dia:g}" if ln.dia else "管线段")
        L = sum(seg_lens(ln.pts))
        self.attr.insert("end", f"\n几何长度: {L:.2f} m")
        if self.mode == "2d":
            for pgid in (ln.st, ln.ed):
                p = self.pt_map.get(pgid)
                if p and p.x is not None:
                    x, y = self._to_canvas(p.x, p.y)
                    self.sel_marks.append(self.canvas.create_oval(
                        x - 10, y - 10, x + 10, y + 10, outline="#2ecc71", width=2))
        self.var_status.set(f"管线段 {ln.type} Φ{ln.dia:g}mm 长 {L:.2f}m — 可点上方[纵断面]")

    def show_profile(self):
        if self.sel_line:
            tr = [(self.sel_line, False)]
            ProfileWin(self.root, [tr], [self.sel_line], self.pt_map, self.font_size)

    # ───── 拉框选线纵断面 ─────
    def start_box_profile(self):
        if self.mode != "2d":
            messagebox.showinfo("提示", "拉框选线请在 2D 平面模式下使用（先切换回 2D）")
            return
        self.box_sel = not self.box_sel
        self.canvas.config(cursor="crosshair" if self.box_sel else "")
        if self.box_sel:
            self.var_status.set("拉框选线：在平面图上按住左键拖出矩形，松开后框内管线自动串接绘制纵断面"
                                "（Esc 或再点按钮取消）")
        else:
            self._cancel_box()

    def _cancel_box(self, e=None):
        if self.box_sel or self.box_start or self.rect_id:
            self.box_sel = False
            self.box_start = None
            if self.rect_id:
                self.canvas.delete(self.rect_id)
                self.rect_id = None
            self.canvas.config(cursor="")
            self.var_status.set("已取消拉框选线")

    def _from_canvas(self, sx, sy):
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        return (self.cx + (h / 2 - sy) / self.scale,
                self.cy + (sx - w / 2) / self.scale)

    def _finish_box(self, sx0, sy0, sx1, sy1):
        n0, e0 = self._from_canvas(min(sx0, sx1), min(sy0, sy1))
        n1, e1 = self._from_canvas(max(sx0, sx1), max(sy0, sy1))
        sel = [ln for ln in self.lines
               if any(n0 <= p[0] <= n1 and e0 <= p[1] <= e1 for p in ln.pts)]
        self.box_sel = False
        self.canvas.config(cursor="")
        if not sel:
            self.var_status.set("框选范围内未包含管线段")
            return
        tracks = chain_tracks(sel)
        ProfileWin(self.root, tracks, sel, self.pt_map, self.font_size)
        self.var_status.set(f"框选 {len(sel)} 条管线段，按节点串接为 {len(tracks)} 条路径绘制纵断面")

    # ───── 表格 ─────
    def _fill_tables(self):
        self.tv_lines.delete(*self.tv_lines.get_children())
        for i, ln in enumerate(self.lines, 1):
            L = sum(seg_lens(ln.pts))
            sp = self.pt_map.get(ln.st)
            self.tv_lines.insert("", "end", iid=ln.gid, values=(
                i, ln.type, f"{ln.dia:g}" if ln.dia else "", ln.gid[:8],
                f"{sp.x:.3f}" if sp and sp.x is not None else "",
                f"{sp.y:.3f}" if sp and sp.y is not None else "",
                f"{sp.ground_h:.3f}" if sp and sp.ground_h is not None else "",
                "", f"长{L:.1f}m 埋深{ln.sdeep}~{ln.edeep}"))
        self.tv_points.delete(*self.tv_points.get_children())
        for i, p in enumerate(self.points, 1):
            self.tv_points.insert("", "end", iid=p.gid, values=(
                i, p.type, "", p.name or p.gid[:8],
                f"{p.x:.3f}" if p.x is not None else "",
                f"{p.y:.3f}" if p.y is not None else "",
                f"{p.ground_h:.3f}" if p.ground_h is not None else "",
                f"{p.bottom_h:.3f}" if p.bottom_h is not None else "",
                "实测" if str(p.source) == "1" else "连接既有"))

    def _fill_stats(self):
        self.tv_stat.delete(*self.tv_stat.get_children())
        rows, total = compute_stats(self.lines)
        for r in rows:
            self.tv_stat.insert("", "end", values=(
                TYPE_NAME.get(r["type"], r["type"]), f"{r['dia']:g}",
                r["count"], f"{r['len']:.1f}", f"{r['pct']:.1f}%"))
        self.tv_stat.insert("", "end", values=("合计", "", len(self.lines),
                                               f"{total:.1f}", "100%"))
        self.stat_txt.delete("1.0", "end")
        self.stat_txt.insert("end", "统计结论：\n" + stats_conclusion(self.lines, rows, total))

    def _fill_summary(self):
        self.tv_summ.delete(*self.tv_summ.get_children())
        for k, v in compute_summary(self.lines, self.points):
            self.tv_summ.insert("", "end", values=(k, v))

    def _table_pick(self, e):
        tv = e.widget
        sel = tv.selection()
        if not sel:
            return
        gid = sel[0]
        if tv is self.tv_points:
            self._show_pt(gid)
            obj = next((q for q in self.points if q.gid == gid), None)
        else:
            self._show_line(gid)
            obj = next((q for q in self.lines if q.gid == gid), None)
        if obj:
            if hasattr(obj, "pts"):
                xs = [p[0] for p in obj.pts]
                ys = [p[1] for p in obj.pts]
                self.cx, self.cy = sum(xs) / len(xs), sum(ys) / len(ys)
            else:
                self.cx, self.cy = obj.x, obj.y
            self.redraw()

    # ───── 撞管 ─────
    def do_clash(self):
        if not self.lines:
            return
        try:
            gap = float(self.var_clear.get())
        except ValueError:
            gap = 0.3
        self.var_status.set("撞管检测中…")
        self.root.update()
        self.clashes = clash_detect(self.lines, self.points, gap)
        self.tv_clash.delete(*self.tv_clash.get_children())
        for i, c in enumerate(self.clashes, 1):
            a, b = c["l1"], c["l2"]
            gap_txt = f"{c['gap']:+.2f}" if c["gap"] is not None else "-"
            tag = ("⚠ " if c["kind"] == "clash" else "△ " if c["kind"] == "warn"
                   else "? " if c["kind"] == "unknown" else "")
            self.tv_clash.insert("", "end", iid=str(i), values=(
                i, tag + KIND_TXT[c["kind"]],
                f"{TYPE_NAME.get(a.type, a.type)} Φ{a.dia:g}",
                f"{TYPE_NAME.get(b.type, b.type)} Φ{b.dia:g}",
                gap_txt, f"{c['pos'][1]:.2f}, {c['pos'][0]:.2f}"))
        # 结果表停靠在平面图下方（同屏看平面）
        self.clash_frame.pack_forget()
        self.clash_frame.pack(fill="x", side="bottom")
        n_clash = sum(1 for c in self.clashes if c["kind"] == "clash")
        n_warn = sum(1 for c in self.clashes if c["kind"] == "warn")
        n_unk = sum(1 for c in self.clashes if c["kind"] == "unknown")
        self.var_status.set(
            f"撞管检测完成：交叉 {len(self.clashes)} 处 — 撞管 {n_clash}、净距不足 {n_warn}、"
            f"缺高程 {n_unk}。点击下表行可在平面/三维中定位；可[导出DXF]或出[撞管报告]")
        self.redraw()

    def _clash_pick(self, e):
        sel = self.tv_clash.selection()
        if not sel:
            return
        c = self.clashes[int(sel[0]) - 1]
        self.cx, self.cy = c["pos"][0], c["pos"][1]
        self.scale = max(self.scale, 8)
        self.redraw()
        a, b = c["l1"], c["l2"]
        self._show_attrs({
            "管线①": f"{TYPE_NAME.get(a.type, a.type)} Φ{a.dia:g} "
                     + (f"管底≈{c['b1']:.3f}" if c["b1"] is not None else "缺高程"),
            "管线②": f"{TYPE_NAME.get(b.type, b.type)} Φ{b.dia:g} "
                     + (f"管底≈{c['b2']:.3f}" if c["b2"] is not None else "缺高程"),
            "垂直净距": f"{c['gap']:+.3f} m（负=立面重叠）" if c["gap"] is not None else "-",
            "判定": {"clash": "撞管（立面重叠）", "warn": "净距不足",
                    "ok": "正常", "unknown": "缺少端点高程"}[c["kind"]],
            "位置": f"东 {c['pos'][1]:.3f} / 北 {c['pos'][0]:.3f}",
        }, f"交叉点 #{sel[0]}")

    # ───── 导出 ─────
    def _ask_save(self, default, ftypes):
        return filedialog.asksaveasfilename(initialfile=default, filetypes=ftypes)

    def exp_dxf(self):
        p = self._ask_save("管线图_含风险点.dxf", [("DXF", "*.dxf")])
        if not p:
            return
        try:
            export_dxf(self.lines, self.points, self.clashes, p)
            self.var_status.set(f"DXF 已导出：{p}（风险点红色标记，管线按类别分层）")
        except Exception as e:
            messagebox.showerror("错误", str(e))

    def exp_clash_rep(self):
        if not self.clashes:
            self.do_clash()
        p = self._ask_save("撞管检测报告.html", [("HTML", "*.html")])
        if not p:
            return
        build_clash_html(self.lines, self.points, self.clashes, p)
        self.var_status.set(f"撞管检测报告已导出：{p}")

    def exp_stats(self):
        p = self._ask_save("管线长度统计报表.html", [("HTML", "*.html")])
        if not p:
            return
        rows, total = compute_stats(self.lines)
        build_stats_html(self.lines, rows, total, p)
        self.var_status.set(f"统计报表已导出：{p}")

    def exp_summary(self):
        p = self._ask_save("管线长度汇总表.html", [("HTML", "*.html")])
        if not p:
            return
        build_summary_html(self.lines, self.points, p)
        self.var_status.set(f"长度表已导出：{p}")

    def exp_shp(self):
        d = filedialog.askdirectory(title="选择导出文件夹（生成 管线L.shp 与 管点P.shp）")
        if not d:
            return
        try:
            export_shp(self.lines, self.points, self.schemas, self.prj_txt, d)
            n_l = sum(1 for _ in self.lines)
            n_p = sum(1 for p in self.points if p.x is not None)
            self.var_status.set(f"SHP 已导出：{d}（管线L {n_l} 条 / 管点P {n_p} 个，"
                                f"字段结构同入库数据，含坐标系 .prj）")
        except Exception as e:
            messagebox.showerror("错误", f"SHP 导出失败：{e}")

    # ───── 新增：最近文件夹 / 关于 / 图层显隐 / 定位 / 撞管CSV ─────
    def _refresh_recent(self):
        try:
            self.recent_menu.delete(0, "end")
        except Exception:
            return
        if not self.recent:
            self.recent_menu.add_command(label="（无）", state="disabled")
            return
        for d in self.recent:
            self.recent_menu.add_command(label=d, command=lambda d=d: self._load_folder(d))

    def _about(self):
        messagebox.showinfo("关于",
            f"GXGC 管线数据库可视化与撞管分析系统\n版本 {VERSION}\n\n"
            "作者：黄波  QQ：799144685\n\n"
            "SHP 读取 / 2D-3D 浏览 / 撞管检测 / 纵断面 /\n"
            "DXF·SHP·报告(HTML)·撞管(CSV) 导出\n\n"
            "v2.2 新增：最近文件夹记忆、撞管结果 CSV 导出、\n"
            "按管线类型显隐图层、按点号/GID 定位")

    def _build_type_filter(self):
        for w in list(self.type_frame.winfo_children())[1:]:
            w.destroy()
        self.type_hide = set()
        self.type_vars = {}
        types = sorted({ln.type for ln in self.lines if ln.type} |
                      {p.type for p in self.points if p.type})
        if not types:
            return
        grid = ttk.Frame(self.type_frame)
        grid.pack(fill="x", padx=6, pady=2)
        for i, t in enumerate(types):
            v = tk.BooleanVar(value=(t not in self.type_hide))
            self.type_vars[t] = v
            ttk.Checkbutton(grid, text=TYPE_NAME.get(t, t),
                           variable=v, command=self._toggle_type
                           ).grid(row=i // 2, column=i % 2, sticky="w", padx=6)

    def _toggle_type(self):
        self.type_hide = {t for t, v in self.type_vars.items() if not v.get()}
        self.redraw()

    def _locate(self):
        if not (self.lines or self.points):
            return
        q = self.var_find.get().strip().upper()
        if not q:
            return
        hit = next((p for p in self.points
                    if (p.name and q in p.name.upper()) or q in p.gid), None)
        if not hit:
            hit = next((ln for ln in self.lines if q in ln.gid), None)
        if not hit:
            self.var_status.set(f"未找到匹配「{self.var_find.get()}」的管点/管线段")
            return
        if hasattr(hit, "pts"):
            xs = [p[0] for p in hit.pts]
            ys = [p[1] for p in hit.pts]
            self.cx, self.cy = sum(xs) / len(xs), sum(ys) / len(ys)
            self._show_line(hit.gid)
        else:
            self.cx, self.cy = hit.x, hit.y
            self._show_pt(hit.gid)
        self.scale = max(self.scale, 10)
        self.redraw()
        self.var_status.set(f"已定位：{hit.name or hit.gid[:8]}")

    def exp_clash_csv(self):
        if not self.clashes:
            messagebox.showinfo("提示", "请先执行撞管检测（点工具栏「撞管检测」）")
            return
        p = self._ask_save("撞管检测结果.csv", [("CSV", "*.csv")])
        if not p:
            return
        try:
            import csv
            with open(p, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f)
                w.writerow(["序号", "判定", "管线①类型", "管线①管径mm", "管线②类型",
                            "管线②管径mm", "管线①管底标高", "管线②管底标高",
                            "垂直净距(m)", "交叉位置_东", "交叉位置_北"])
                for i, c in enumerate(self.clashes, 1):
                    a, b = c["l1"], c["l2"]
                    w.writerow([
                        i, KIND_TXT[c["kind"]],
                        TYPE_NAME.get(a.type, a.type), f"{a.dia:g}",
                        TYPE_NAME.get(b.type, b.type), f"{b.dia:g}",
                        f'{c["b1"]:.3f}' if c["b1"] is not None else "",
                        f'{c["b2"]:.3f}' if c["b2"] is not None else "",
                        f'{c["gap"]:+.3f}' if c["gap"] is not None else "",
                        f'{c["pos"][1]:.3f}', f'{c["pos"][0]:.3f}'])
            self.var_status.set(f"撞管结果 CSV 已导出：{p}（UTF-8-SIG，Excel 可直接打开）")
        except Exception as e:
            messagebox.showerror("错误", str(e))


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
