#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/quick-maths:0.2.1": shorthands



RULES FOR w:t :


#let w_base_case(wit: $w$, typ: $b$, con: $c$) = rule(
  name: [Base],
  [$[|wit|] = {con}$],
  [$con in [|typ|]$],
  [$|- wit : typ$],
)

#let w_arrow(wit: $w$, t_1: $t_1$, t_2: $t_2$) = rule(
  name: [$->$],
  [$|- w lt.eq.slant t_1 -> t_2$],
  [$|- w : t_1 -> t_2$],
)

#let w_and(wit: $w$, t_1: $t_1$, t_2: $t_2$) = rule(
  name: [$and$],
  [$|- w : t_1$],
  [$|- w : t_2$],
  [$|- w : t_1 and t_2$],
)

#let w_or_1(wit: $w$, t_1: $t_1$, t_2: $t_2$) = rule(
  name: [$or_1$],
  [$|- w : t_1$],
  [$|- w : t_1 or t_2$],
)

#let w_or_2(wit: $w$, t_1: $t_1$, t_2: $t_2$) = rule(
  name: [$or_2$],
  [$|- w : t_2$],
  [$|- w : t_1 or t_2$],
)

#let w_tuple(wit: $w$, w_1: $w_1$, w_2: $w_2$, t_1: $t_1$, t_2: $t_2$) = rule(
  name: [Tuple],
  [$|- w_1 : t_1$],
  [$|- w_2 : t_2$],
  [$|- (w_1 * w_2) : (t_1 * t_2)$],
)

#let rule_w = align(center, rule-set(
  prooftree(w_base_case()),
  prooftree(w_arrow()),
  prooftree(w_or_1()),
  prooftree(w_or_2()),
  prooftree(w_and()),
  prooftree(w_tuple()),
))


RULES FOR $t ~> w$ :

#let t_base(Delta: $Delta$, typ: $b$, wit: $w$) = rule(
  name: [Base],
  [???????],
  [$Delta |-""_s typ ~> wit$],
)

#let t_arrow(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$) = rule(
  name: [$->$],
  [????????????],
  [$Delta |-""_s typ1 -> typ2 ~> wit$],
)

#let t_tuple(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit1: $w_1$, wit2: $w_2$) = rule(
  name: [$*$],
  [$Delta |-""_m  typ1 ~> wit1$],
  [$Delta |-""_m typ2 ~> wit2$],
  [$Delta |-""_s typ1 * typ2 ~> wit1 * wit2$]
)

#let t_or_1(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$) = rule(
  name:[$or_1$],
  [$Delta |-""_m typ1 ~> wit$],
  [$Delta |-""_s typ1 or typ2 ~> wit$]
)

#let t_or_2(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$) = rule(
  name:[$or_2$],
  [$Delta |-""_m typ2 ~> wit$],
  [$Delta |-""_s typ1 or typ2 ~> wit$]
)

#let t_mem(Delta: $Delta$, typ : $t$, wit: $w$) = rule(
  name:[$typ in.not Delta$],
  [$Delta union {typ}|-""_s  typ ~> wit$],
  [$Delta |-""_m typ ~> wit$]
)

#let rule_t = align(center, rule-set(
  prooftree(t_base()),
  prooftree(t_arrow()),
  prooftree(t_tuple()),
  prooftree(t_or_1()),
  prooftree(t_or_2()),
  prooftree(t_mem())
))