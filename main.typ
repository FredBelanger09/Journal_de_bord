#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands

#import "macros.typ": BeauB, BeauC, BigOne, BigZero, not_temoin
#import "rules.typ": rule_w, rule_t, exemple_t1, exemple_w1

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

== Définition de $w:t$
On veut définir un prédicat $w : t$ qui est vrai si et seulement si w est un témoin de t, avec les règles suivantes :

#rule_w


== Définition de $t ~> w$
On peut ensuite décrire le fonctionnement de l'algorithme qui pour chaque type t associe un témoin w (qu'on notera $t ~> w$) qui a les règles suivantes :

#rule_t

==== Exemple :
On a $t = ("Int", ("Int" -> "Bool") or ("Bool" -> "Int"))$

Cela nous donne l'arbre :

#exemple_t1

On peut ainsi vérifier que $w = (42, "Int" -> BigZero)$ est bien un témoin de $ t = ("Int", ("Int" -> "Bool") or ("Bool" -> "Int"))$

#exemple_w1


== Preuve de la terminaison de $t ~> w$

On peut déjà noter que pour tout type t, $Delta$ a une taille maximale finie, car il est au maximum de la taille l'ensemble de tout les sous-types de t (qui sont, par définition de t, finis).

En peut aussi dire qu'en pratique, nos types sont stockés sous la forme de DNF, on a donc :

$ t = or.big (and.big b) or.big (and.big (t_1 * t_2)) or.big (and.big t_1 -> t_2) $

Les cas de b et A ne sont pas récursifs, il finissent donc forcément.

On a aussi un résultat qui dit que $forall t , t lt.eq.slant BigOne * BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$

Or $(t_1 *t_2) and (t_3 * t_4) = (t_1 and t_3 * t_2 and t_4)$, donc $and.big (t_1 * t_2) = (and.big t_1 * and.big t_2) lt.eq.slant BigOne * BigOne$, donc $and.big (t_1 * t_2) = or.big (t'_1, t'_2)$









= Expliquer ça à des canards 

On a des types ensemblistes $t = "Int" | "Enum" | t or t | t and t | not t | t * t | t -> t | BigZero "(l'ensemble vide)" | BigOne "(L'ensemble de tout les types)"$. On veut prouver que pour tout type non-vide, on peut créer un témoin de t. Un témoin est une constante appartenant à t (genre pour t = Int, on aura w=42, t=(Bool, $[16,+ infinity[$) donnera w= (True, 16), etc).Le seul cas spécial est si $t = t_1 -> t_2$, alors on ne cherche pas à trouver des témoin de $t_1$ et $t_2$ et on renvoie juste $w = t_1 -> t_2$ (en gros).

On veut donc :
- Définir $w:t$ (w est un témoin de t) avec des règles d'inférences
- définir $Delta |-""_m t ~> w$ (Dans l'environnement $Delta$, t produit w avec notre algorithme)
- Montrer la terminaison de $Delta |-""_m t ~> w$
- Montrer que si $emptyset |- ""_m t ~> w$ alors $w:t$

NB : dans notre algo $t ~> w$, $ Delta$ est un outil de mémoïsation afin de détecter les définitions récursives.

Les règle d'inférences actuelles sont :

Pour $w:t$ :
#rule_w

Pour $Delta |- t ~> w$ :
#rule_t

Problème 1 : ces définitions sont vachements similaires, donc le si $t~> w$ alors $w:t$ fait très raisonnement circulaire

Problème 2 : Je peux prouver la terminaison car $Delta$ a une taille max finie et augmente à chaque étape, mais je sais pas comment formaliser ça

Problème 3 : J'arrive pas à faire le raisonnement par induction pour la dernière partie


Pour 



#pagebreak()










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

