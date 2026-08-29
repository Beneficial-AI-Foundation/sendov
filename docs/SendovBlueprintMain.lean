import VersoManual
import VersoBlueprint.PreviewManifest
import SendovBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/-- Static images (Tao's diagrams) are copied to `site/<format>/figures/` and scaled to the column. -/
def renderConfig : RenderConfig where
  extraFiles := [("SendovBlueprint/figures", "figures")]
  extraHead := #[.tag "style" #[] (.text false
    "main img { max-width: 100%; height: auto; display: block; margin: 1em auto; }")]

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SendovBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := renderConfig)
