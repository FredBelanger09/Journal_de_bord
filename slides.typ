#import "@preview/pepentation:0.2.0": *


#import "macros.typ" : *

#set text(lang: "fr")

#let my-custom-theme = (
  primary: rgb("#dc2626"),
  secondary: rgb("#00649F"),
  background: rgb("#FFFFFF"),
  main-text: rgb("#000000"),
  sub-text: rgb("#FFFFFF"),
  sub-text-dimmed: rgb("#FFFFFF"),
  code-background: luma(240),
  code-text: none,
  blocks: (
    definition-color: gray,
    warning-color: red,
    remark-color: orange,
    hint-color: green,
    info-color: blue,
    example-color: purple,
    quote-color: luma(200),
    success-color: rgb("#22c55e"),
    failure-color: rgb("#ef4444"),
  ),
)





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
  locale: "EN",
  theme: my-custom-theme ,
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

== SSTT

Blablabla les types ensemblistes c'est assez niche mais c'est déjà utilisé dans les langage comme Elixir, Erlang ou encore la génération de message d'erreur dans Roblox.

== Motivation

appliquer x de type t à f de type $u -> v$ ne peut se faire que si $t lt.eq.slant u$, donc si $t \\u = emptyset$. Si $u \\t != emptyset$, patatra !

= Génération de témoin

== Witness

Un témoin c'est un type singleton OU un type flèche, pourquoi ? Parce que le type t -> s c'est chiant d'en trouver un witness


== Preuve de sûreté

#definition[
  nlsfzz
]

== Extensions


= Types polymorphe

== Tallying


== Exemple

$t =(alpha^1, not alpha^1) \\ (alpha^2, alpha^3)$


#grid(

  columns: 4,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^1$], [$alpha^2$], [$alpha^3$],
  [$sigma_1$], [$BigZero, BigZero$], [$BigZero,BigOne$], [$BigZero,BigOne$],
  [$sigma_2$], [$BigOne,BigOne$], [$BigZero,BigOne$], [$BigZero,BigOne$],
  [$sigma_3$], [$not alpha^3, not alpha^3 or alpha^2$], [$not alpha^3, BigOne$], [$BigZero, BigOne$],
)


#grid(
  columns: 2,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^3$],
  [$sigma_1$], [$BigOne, BigOne$],
)

#grid(
  columns: 1,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [$alpha^3$],
  [$BigOne, BigOne$],
)
