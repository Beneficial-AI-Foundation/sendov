#!/usr/bin/env python3
"""Generate docs/SendovBlueprint/Figures/Data.lean: clickable overlays for Tao's two diagrams.

The diagrams themselves (docs/SendovBlueprint/figures/*.png, from Section 2.2 of the blog post)
are shown unchanged.  This script only computes *where* each curve, region and legend entry lies
in image pixels and emits invisible SVG hotspots on top of the PNG, each naming the blueprint
node that proves it.  The Lean side (Figures.lean) turns node names into links at render time.

Calibration: the axes frame is detected from the PNG; the curve formulas are the blog's, and the
script asserts that the predicted curve pixels really are the right colour in the image, so a
misplacement fails the run instead of shipping.

Run from docs/:  python3 scripts/gen_figure_hotspots.py   (needs numpy, pillow)
"""
import os
import numpy as np
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
FIGDIR = os.path.join(HERE, "..", "SendovBlueprint", "figures")
OUT = os.path.join(HERE, "..", "SendovBlueprint", "Figures", "Data.lean")

# ------------------------------------------------------------------ curve formulas (blog §2.2)
def polar_rat(a): return a / (3 + a)                       # (18), rational half
def polar_log(a): return 1 - np.log(a) / a                 # (18), logarithmic half
def origin_asym(a):                                        # (21) with error terms dropped
    return ((3 + 4 * a) - np.sqrt((3 + 4 * a) ** 2 - 16 * a)) / 2
def polar_exact(a):                                        # boundary of (17), by bisection
    lo, hi = 1e-9, 1 - 1e-9
    f = lambda b: np.exp(-a) * (np.exp(a * (2 - b)) - 1) / (a * (2 - b)) - 1
    for _ in range(80):
        mid = (lo + hi) / 2
        if f(mid) > 0: lo = mid
        else: hi = mid
    return (lo + hi) / 2

AL = np.concatenate([np.linspace(0.01, 1, 40), np.linspace(1, 20, 120)[1:]])

# ------------------------------------------------------------------ image helpers
def load(name):
    im = Image.open(os.path.join(FIGDIR, name)).convert("RGB")
    return np.asarray(im)

def frame(rgb):
    g = rgb.mean(axis=2)
    dark = g < 90
    cols = np.where(dark.sum(0) > 0.6 * rgb.shape[0])[0]
    rows = np.where(dark.sum(1) > 0.6 * rgb.shape[1])[0]
    return cols.min(), cols.max(), rows.max(), rows.min()   # x0, x1, y(beta=0), y(beta=1)

class Cal:
    def __init__(self, rgb):
        self.h, self.w = rgb.shape[:2]
        self.x0, self.x1, self.yb0, self.yb1 = frame(rgb)
        self.rgb = rgb
    def sx(self, a): return self.x0 + (self.x1 - self.x0) * a / 20.0
    def sy(self, b): return self.yb0 - (self.yb0 - self.yb1) * b
    def check(self, alphas, betas, pred, what):
        """assert that most predicted curve pixels satisfy the colour predicate `pred`."""
        hits = 0; n = 0
        for a, b in zip(alphas, betas):
            if not (0 <= b <= 1): continue
            x, y = int(round(self.sx(a))), int(round(self.sy(b)))
            patch = self.rgb[max(0, y - 3):y + 4, max(0, x - 3):x + 4].reshape(-1, 3)
            n += 1
            if any(pred(p) for p in patch): hits += 1
        frac = hits / n
        print(f"  {what}: {hits}/{n} predicted pixels match ({frac:.0%})")
        assert frac > 0.9, f"calibration failed for {what}"

is_blue = lambda p: p[2] > 150 and p[0] < 110 and p[1] < 110
is_red = lambda p: p[0] > 180 and p[1] < 110 and p[2] < 110
is_green = lambda p: p[1] > 90 and p[0] < 90 and p[2] < 90

# ------------------------------------------------------------------ Lean emission
def lstr(s): return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
def tag(name, attrs, children=()):
    a = ", ".join(f"({lstr(k)}, {lstr(str(v))})" for k, v in attrs.items())
    return f".tag {lstr(name)} #[{a}] #[{', '.join(children)}]"
def link(node, title, children):
    return f".link {lstr(node)} {lstr(title)} #[{', '.join(children)}]"
def fmt(v): return f"{v:.1f}"

def path_d(cal, alphas, betas, close_to=None):
    p = [(cal.sx(a), cal.sy(min(max(b, -0.02), 1.02))) for a, b in zip(alphas, betas)]
    d = "M" + " L".join(f"{x:.1f},{y:.1f}" for x, y in p)
    if close_to is not None:
        d += f" L{p[-1][0]:.1f},{cal.sy(close_to):.1f} L{p[0][0]:.1f},{cal.sy(close_to):.1f} Z"
    return d

def curve(cal, node, title, alphas, betas, cls):
    return link(node, title, [tag("path", {"d": path_d(cal, alphas, betas), "class": f"hot curve {cls}"})])
def region(cal, node, title, alphas, betas, close_to, cls):
    return link(node, title, [tag("path", {"d": path_d(cal, alphas, betas, close_to), "class": f"hot region {cls}"})])
def legend_row(node, title, x, y, w, h):
    return link(node, title, [tag("rect", {"x": fmt(x), "y": fmt(y), "width": fmt(w), "height": fmt(h), "class": "hot legend"})])

def svg(png, cal, children):
    return tag("svg", {"viewBox": f"0 0 {cal.w} {cal.h}", "xmlns": "http://www.w3.org/2000/svg",
                       "xmlns:xlink": "http://www.w3.org/1999/xlink", "class": "sendov-fig"},
               [tag("image", {"href": f"/figures/{png}", "x": "0", "y": "0", "width": str(cal.w), "height": str(cal.h)})] + children)

# ------------------------------------------------------------------ figure 1: polar region (17) + bounds (18)
png1 = "tao-polar-region.png"
c1 = Cal(load(png1))
print(png1, "frame", c1.x0, c1.x1, c1.yb0, c1.yb1)
al = AL
p_rat, p_log, p_ex = polar_rat(al), polar_log(al), np.array([polar_exact(a) for a in al])
c1.check(al[al > 1.0], p_rat[al > 1.0], is_red, "beta = alpha/(3+alpha) (drawn red in this diagram)")
m = (p_log <= 1.0) & (al > 1.2)
c1.check(al[m], p_log[m], is_green, "beta = 1 - log(alpha)/alpha (green)")
fig1 = [
    region(c1, "in_polar_exp", "Feasible region of the exponential polar inequality (17) — in_polar_exp", al, p_ex, 0.0, "polar"),
    curve(c1, "in_beta_bound", "β(1) ≤ α/(3+α), rational half of (18) — in_beta_bound", al, p_rat, "rat"),
    curve(c1, "in_beta_bound", "β(1) ≤ 1 − log α / α, logarithmic half of (18) — in_beta_bound", al[p_log <= 1.02], p_log[p_log <= 1.02], "log"),
    legend_row("in_polar_exp", "in_polar_exp", 1245, 728, 295, 34),
    legend_row("in_beta_bound", "in_beta_bound", 1245, 764, 295, 36),
    legend_row("in_beta_bound", "in_beta_bound", 1245, 804, 295, 42),
]

# ------------------------------------------------------------------ figure 2: polar vs origin
png2 = "tao-polar-vs-origin.png"
c2 = Cal(load(png2))
print(png2, "frame", c2.x0, c2.x1, c2.yb0, c2.yb1)
o_asym = origin_asym(al)
c2.check(al[al > 0.5], p_ex[al > 0.5], is_blue, "polar boundary (blue) = exact boundary of (17)")
c2.check(al[al > 0.5], o_asym[al > 0.5], is_red, "origin boundary (red)")
gap = float((o_asym - p_ex).min())
print(f"  min vertical gap between the two boundaries: {gap:.4f}")
assert gap > 0
fig2 = [
    region(c2, "in_polar_exp", "Polar feasible region: where (17) can hold — in_polar_exp", al, p_ex, 0.0, "polar"),
    region(c2, "in_one_le", "Origin feasible region: (21) with its error terms dropped — in_one_le", al, o_asym, 1.0, "origin"),
    curve(c2, "in_polar_exp", "Polar boundary: where equality holds in (17) — in_polar_exp", al, p_ex, "rat"),
    curve(c2, "in_one_le", "Origin boundary, asymptotic form of (21) — in_one_le", al, o_asym, "origin"),
    legend_row("in_polar_exp", "in_polar_exp", 1240, 396, 300, 32),
    legend_row("in_one_le", "in_one_le", 1240, 428, 300, 32),
    legend_row("in_polar_exp", "in_polar_exp", 1240, 460, 300, 32),
    legend_row("in_one_le", "in_one_le", 1240, 492, 300, 32),
]

with open(OUT, "w") as f:
    f.write("-- GENERATED by docs/scripts/gen_figure_hotspots.py; do not edit by hand.\n")
    f.write("import SendovBlueprint.Figures.Svg\n\nnamespace SendovBlueprint.Figures\n\nopen SvgEl\n\n")
    f.write("/-- Blog §2.2, first diagram: the polar feasible region and the two halves of (18). -/\n")
    f.write("def polarRegion : SvgEl :=\n  " + svg(png1, c1, fig1) + "\n\n")
    f.write(f"/-- Blog §2.2, second diagram: polar vs origin feasible regions (min gap {gap:.4f}). -/\n")
    f.write("def polarVsOrigin : SvgEl :=\n  " + svg(png2, c2, fig2) + "\n\n")
    f.write('def figures : List (String × SvgEl) :=\n  [("polar", polarRegion), ("channels", polarVsOrigin)]\n\n')
    f.write("end SendovBlueprint.Figures\n")
print("wrote", OUT, os.path.getsize(OUT), "bytes")
