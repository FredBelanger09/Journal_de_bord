#import "@preview/pepentation:0.2.0": *

#set text(lang: "fr")
#show: setup-presentation.with(
  title-slide: (
    enable: true,
    title: "Calcul de témoin pour les types ensemblistes",
    authors: ("Félix Belanger",),
    institute: "Université Paris Saclay",
  ),
  footer: (
    enable: true,
    title: "Témoin de types ensemblistes",
    institute: "LMF",
    authors: ("Belanger",),
  ),
  table-of-contents: "simple",
  header: true,
  locale: "EN"
)

= Introduction

== Slide Title

This is a slide with a title

#lorem(100)

//If no title is provided it will not be shown in table of content
==

This is slide with no title

#lorem(100)

= Types ensemblistes

== Greatest common divisor

#text(size: 0.95em)[
  #definition[
    *Definition – Euclid's algorithm*

    The function `gcd(a, b)` returns the greatest common divisor of two integers.
  ]

  #warning[
    *Warning – undefined case*

    `gcd(a, 0)` is fine, but `gcd(0, 0)` is mathematically undefined.
    Your implementation should reject or handle this explicitly
  ]

  #remark[
    *Remark – symmetry property*

    `gcd(a, b)` should always equal `gcd(b, a)`. You can use this to test
    your implementation
  ]

  #hint[
    *Hint – simplifying fractions with gcd*

    Once `gcd(a,b)` works, you can reduce fractions to lowest terms
  ]
]


= Génération de témoin

== Witness

== Preuve de sûreté

== Extensions


= Types polymorphe

== Tallying

== Exemple

