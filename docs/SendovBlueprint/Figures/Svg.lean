import Verso
import VersoManual
import VersoBlueprint

/-!
# Clickable overlays for figures

A tiny SVG element tree whose `link` nodes name blueprint nodes rather than URLs.  At HTML
render time the links are resolved through the same table `{bpref ...}` uses, so a curve in
a figure is a way into the proposition that proves it, and survives chapter reordering.
The figure itself is an unmodified PNG (`<image>`); only invisible hotspots are drawn on top.
-/

namespace SendovBlueprint.Figures

inductive SvgEl where
  | tag (name : String) (attrs : Array (String × String)) (children : Array SvgEl)
  | text (s : String)
  | link (node : String) (title : String) (children : Array SvgEl)
deriving Repr, Inhabited

end SendovBlueprint.Figures
