#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands

#import "macros.typ": BeauB, BeauC, BigOne, BigZero, not_temoin
#import "rules.typ": rule_w, rule_t, exemple_t1, exemple_w1, rule_w, w_base, w_arrow, w_tuple, t_base,t_arrow, t_mem, t_or_1, t_or_2, t_tuple

#show: shorthands.with(($|-$, $tack.r$))
#show : text(lang : "fr")
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

= Expliquer ça à des canards 

On a des types ensemblistes $t = "Int" | "Enum" | t or t | t and t | not t | t * t | t -> t | BigZero "(l'ensemble vide)" | BigOne "(L'ensemble de tout les types)"$. On veut prouver que pour tout type non-vide, on peut créer un témoin de t. Un témoin est une constante appartenant à t (genre pour t = Int, on aura w=42, t=(Bool, $[16,+ oo[$) donnera w= (True, 16), etc).Le seul cas spécial est si $t = t_1 -> t_2$, alors on ne cherche pas à trouver des témoin de $t_1$ et $t_2$ et on renvoie juste $w = t_1 -> t_2$ (en gros).

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

