import Verso
import VersoManual
import VersoBlueprint
import SendovBlueprint.Figures.Svg
import SendovBlueprint.Figures.Data

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Doc.Html (HtmlT)
open Verso.Output (Html)

namespace SendovBlueprint.Figures

/-- HTML tree; `link` nodes become `<a>` elements pointing at the blueprint node when it
resolves, and stay as plain groups (with the tooltip) otherwise. -/
partial def SvgEl.toHtml (href? : String → Option String) : SvgEl → Html
  | .text s => .text true s
  | .tag name attrs cs => .tag name attrs (.seq (cs.map (toHtml href?)))
  | .link node title cs =>
    let body := .seq (cs.map (toHtml href?))
    let tip : Html := .tag "title" #[] (.text true title)
    match href? node with
    | some href => .tag "a" #[("href", href), ("class", "fig-link"), ("data-node", node)] (.seq #[tip, body])
    | none => .tag "g" #[("class", "fig-link fig-unresolved"), ("data-node", node)] (.seq #[tip, body])

def figureCss : String := r#"
.sendov-figure { margin: 1.5em auto; max-width: 46em; }
.sendov-figure svg { width: 100%; height: auto; display: block; }
.sendov-figure .hot { fill: transparent; stroke: transparent; }
.sendov-figure .hot.curve { fill: none; stroke-width: 22; stroke-linecap: round; stroke-linejoin: round; }
.sendov-figure a.fig-link { cursor: pointer; }
.sendov-figure a.fig-link:hover .hot.curve { stroke: rgba(255, 200, 0, 0.55); }
.sendov-figure a.fig-link:hover .hot.region { fill: rgba(255, 200, 0, 0.22); }
.sendov-figure a.fig-link:hover .hot.legend { fill: rgba(255, 200, 0, 0.35); }
.sendov-figure .caption { font-size: 0.9em; color: #555; margin-top: 0.4em; text-align: center; }
"#

block_extension Block.clickableFigure (name : String) where
  data := Json.str name
  traverse _ _ _ := pure none
  extraCss := [figureCss]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .str name := data
        | reportError "Expected string JSON for clickable figure" *> pure .empty
      let some fig := figures.lookup name
        | reportError s!"Unknown figure '{name}'" *> pure .empty
      let st ← HtmlT.state
      let href? (node : String) : Option String :=
        Informal.TraversalIndex.Nodes.href? st (Name.mkSimple node)
      let caption ← content.mapM blockHtml
      pure {{
        <figure class="sendov-figure">
          {{fig.toHtml href?}}
          <figcaption class="caption">{{caption}}</figcaption>
        </figure>
      }}
  usePackages := ["\\usepackage{graphicx}"]
  toTeX :=
    some <| fun _ go _ data content => do
      let .str name := data
        | reportError "Expected string JSON for clickable figure" *> pure .empty
      let some fig := figures.lookup name
        | reportError s!"Unknown figure '{name}'" *> pure .empty
      -- The PNG behind the overlay: first `<image>` child of the root `<svg>`.
      let png? : Option String := match fig with
        | .tag _ _ cs => cs.findSome? fun
            | .tag "image" attrs _ => (attrs.find? (·.1 == "href")).map (·.2)
            | _ => none
        | _ => none
      let some png := png? | reportError s!"Figure '{name}' has no image" *> pure .empty
      let caption ← content.mapM go
      pure <| .seq #[.raw s!"\\begin\{center}\\includegraphics[width=0.9\\linewidth]\{{png.drop 1}}\\end\{center}\n", .seq caption]

structure FigureConfig where
  name : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `name .string

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩
end

/--
`:::clickable_figure "channels"` inserts one of the blog post's diagrams (`"polar"` or
`"channels"`) with clickable curves; the directive body is the caption.
-/
@[directive]
def clickable_figure : DirectiveExpanderOf FigureConfig
  | config, stxs => do
    unless (figures.lookup config.name).isSome do
      throwError "Unknown figure {repr config.name}; expected one of {figures.map (·.1)}"
    let args ← stxs.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.clickableFigure $(quote config.name)) #[ $[ $args ],* ])

end SendovBlueprint.Figures
