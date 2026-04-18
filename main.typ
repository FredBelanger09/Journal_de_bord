#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands

#import "macros.typ": BeauB, BeauC, BigOne, BigZero, not_temoin
#import "rules.typ": rule_w, rule_t

#show: shorthands.with(($|-$, $tack.r$), ($|1$, $BigOne$), ($|0$, $BigZero$), ($\_:$, not_temoin))

#show: arkheion.with(
  title: "Rapport de stage",
  authors: (
    (name: "Fred Belanger", email: "felix.belanger@universite-paris-saclay.fr", affiliation: ""),
  ),
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: [On a fait des betises sur les problemes de typage],
  date: "16 Avril 2026",
)
#set cite(style: "chicago-author-date")
#show link: underline

= Introduction
Le but du stage a été de créer une fonction permettant, pour tout type non-vide, de trouver un habitant de ce type, appelé témoin. Ce témoin permet d'afficher un exemple lors de la diffusion d'un message d'erreur de mauvais typage.
= Présentation des types

On travaille sur les types ensemblistes
$ t = b | alpha | t -> t | t * t | t or t | t and t | not t | |0 | |1 $
Où $b in BeauB$ sont les cas de bases (en particuliers les constances $c in BeauC$ ) et $alpha in nu$ les variables de types. $BeauB$ est composé de Int (l'ensemble des entiers relatifs) et Enum (l'ensemble des types énumérés, par exemple bool).

Dans un 1er temps, nous allons ignorer les variables de types pour la construction du témoin.
On propose comme type témoin :
$ w = i in [|"Int"|] | e in [|"Enum"|] | t -> t | w * w $
En pratique, nous avons aussi rajouté des extensions pour les tags et les records, ce qui donne
$ w' = w | "tag"(w) | w * w * ... * w | {l_i : w ... l_n : w} $
Les tags, les n-uplets et les records ne sont en réalité que des cas particuliers des tuples, on ne les traitera donc pas sur le plan théorique.



= Algorithm of soundness


On veut définir un prédicat $w : t$ qui est vrai si et seulement si w est un témoin de t. On peut aussi définir son prédicat inverse $w \_: t$.

On peut construire les règles suivantes :

#rule_w

Ce sont les premières règles qu'on a créé, mais elles présentent un problème évident : Si notre équation est récursive (par exemple de la forme $x = ("Int", x) | "Nil"$ ), on peut créer un arbre infini :

#rule_t


On rajoute donc à nos règles un environnement (BON TERME ? PAS SUR) $Delta$ tel que chaque type est ajouté dedans, et une branche peut être exploré seulement si ce type n'est pas déjà dans $Delta$. On note que $Delta$ a forcément une taille maximum finie.


Avec ces nouvelles règles, chaque passage à la règle d'inférence supérieur
On peut ainsi déterminer que l'algorithme termine, car à chaque nouvelle règle, soit $Delta$ grandit, soit on arrive à un terminaison.

En reprenant l'exemple de $x = ("Int", x) or "Nil"$, on ne peut donc pas refaire le même arbre infini :


Le seul arbre possible sera donc :




= En pratique
Notre algorithme va vérifier pour chacun des 6 grandes classes de type (Int, Enum, Arrow, Tag, Tuple, Records) si celle_ci est vide, dans cet ordre. Si elle ne l'est pas, l
== Int
Si t.Int = Int alors 42
Si



==== Paragraph
#lorem(20)

#lorem(20)

= Math

*Inline:* Let $a$, $b$, and $c$ be the side
lengths of right-angled triangle. Then, we know that: $a^2 + b^2 = c^2$

*Block without numbering:*

#math.equation(block: true, numbering: none, [
  $
    sum_(k=1)^n k = (n(n+1)) / 2
  $
])

*Block with numbering:*

As shown in @equation.

$
  sum_(k=1)^n k = (n(n+1)) / 2
$ <equation>

*More information:*
- #link("https://typst.app/docs/reference/math/equation/")


= Citation

You can use citations by using the `#cite` function with the key for the reference and adding a bibliography. Typst supports BibLateX and Hayagriva.

```typst
#bibliography("bibliography.bib")
```

Single citation @Cas05b. Multiple citations @Cas05b @Cas05b. In text #cite(<Cas05b>, form: "prose")

*More information:*
- #link("https://typst.app/docs/reference/meta/bibliography/")
- #link("https://typst.app/docs/reference/meta/cite/")

= Figures and Tables


#figure(
  table(
    align: center,
    columns: (auto, auto),
    row-gutter: (2pt, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [header 1], [header 2],
    [cell 1], [cell 2],
    [cell 3], [cell 4],
  ),
  caption: [#lorem(5)],
) <table>


*More information*

- #link("https://typst.app/docs/reference/meta/figure/")
- #link("https://typst.app/docs/reference/layout/table/")

= Referencing

*More information:*

- #link("https://typst.app/docs/reference/meta/ref/")

= Lists

*Unordered list*

- #lorem(10)
- #lorem(8)

*Numbered list*

+ #lorem(10)
+ #lorem(8)
+ #lorem(12)

*More information:*
- #link("https://typst.app/docs/reference/layout/enum/")
- #link("https://typst.app/docs/reference/meta/cite/")


// Add bibliography and create Bibiliography section
#bibliography("bibliography.bib")

// Create appendix section
#show: arkheion-appendices
=

== Appendix section

#lorem(100)

