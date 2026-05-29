#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/quick-maths:0.2.1": shorthands
#import "macros.typ": *
#show: shorthands.with(
  ($|-m$, $attach(tack.r, br: m)$),
  ($|-s$, $attach(tack.r, br: s)$),
  ($|-a$, $attach(tack.r, br: a)$),
  ($|-$, $tack.r$),
  ($~=$, $tilde.eq$),
)

ALGO POLYW :

#let polyw_algo = $
  polyw (t) = cases(
    {} & "si" Vars(t) = emptyset,
    limits(union.big)_(alpha in Vars(t)) {alpha |-> BigZero } & "si" Tally[(t, BigZero)] = emptyset,
    sigma' r union r & "sinon",
    & " où" & Tally[(t,BigZero)] = {(alpha, sigma(alpha)),...},
    && s = sigma(alpha){alpha <- BigZero},
    && sigma' = {alpha |-> not s},
    && r = polyw(t sigma')
  )
$

#polyw_algo

EXEMPLES FOR POLYW :


#let ex_polyw1 = text( [$polyw(alpha and beta) &-> Tally[(alpha and beta, BigZero)] = {(alpha, BigZero),...} \
&-> s = BigZero{alpha <- BigZero} = BigZero \
&-> sigma' = {alpha |-> not BigZero} = {alpha |-> BigOne} \
& -> r = polyw((alpha and beta) {alpha |-> BigOne}) = polyw(beta) \ \
& -> Tally[(beta, BigZero)] = {(beta, BigZero)} \
&-> s_2 = BigZero{beta <- BigZero} = BigZero \
&-> sigma'_2 = {beta |-> not BigZero} = {beta |-> BigOne} \
& -> r_2 = polyw((beta) {beta |-> BigOne}) = polyw(BigOne) = {} $

$"Donc" polyw(alpha and beta) &= {alpha |-> BigOne} polyw(beta) union polyw(beta) \
&= {alpha |-> BigOne} {beta |-> BigOne} polyw(BigOne) union {beta |-> not BigZero} polyw(BigOne) union polyw(BigOne) \
&= {alpha |-> BigOne} {beta |-> BigOne} {} union {beta |-> BigOne} {} union {} \
&= {alpha |-> BigOne}  union {beta |-> BigOne} \
&= {alpha |-> BigOne, beta |-> BigOne}

$])



#let ex_polyw2 = $polyw(alpha or beta) &-> Tally[(alpha or beta, BigZero)] = {(alpha, BigZero),...} \
&-> s = BigZero{alpha <- BigZero} = BigZero \
&-> sigma' = {alpha |-> not BigZero} = {alpha |-> BigOne} \
& -> r = polyw((alpha or beta) {alpha |-> BigOne}) = polyw(BigOne) \
& -> Vars(BigOne) = emptyset "donc" polyw (alpha or beta) = {alpha |-> BigOne}$

Pour $polyw(alpha and beta)$ :

#ex_polyw1


Pour $polyw(alpha or beta)$ :

#ex_polyw2
