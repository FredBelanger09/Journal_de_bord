#import "@preview/curryst:0.6.0": prooftree, rule, rule-set
#import "@preview/quick-maths:0.2.1": shorthands
#import "macros.typ": BigZero



RULES FOR w:t :


#let w_base_case(typ: $b$, con: $c$) = rule(
  name: [Base],
  [$con in [|typ|]$],
  [$|- con : typ$],
)

#let w_arrow(wit: $w$, typ1: $t_1$, typ2: $t_2$) = rule(
  name: [$->$],
  [$wit lt.eq.slant typ1 -> typ2$],
  [$|- wit : typ1 -> typ2$],
)

#let w_and(wit: $w$, typ1: $t_1$, typ2: $t_2$) = rule(
  name: [$and$],
  [$|- wit : typ1$],
  [$|- wit : typ2$],
  [$|- wit : typ1 and typ2$],
)

#let w_or_1(wit: $w$, typ1: $t_1$, typ2: $t_2$) = rule(
  name: [$or_1$],
  [$|- wit : typ1$],
  [$|- wit : typ1 or typ2$],
)

#let w_or_2(wit: $w$, typ1: $t_1$, typ2: $t_2$) = rule(
  name: [$or_2$],
  [$|- wit : typ2$],
  [$|- wit : typ1 or typ2$],
)

#let w_tuple( wit1: $w_1$, wit2: $w_2$, typ1: $t_1$, typ2: $t_2$) = rule(
  name: [$*$],
  [$|- wit1 : typ1$],
  [$|- wit2 : typ2$],
  [$|- (wit1 * wit2) : (typ1 * typ2)$],
)

#let rule_w = align(center, rule-set(
  prooftree(w_base_case()),
  prooftree(w_arrow()),
  prooftree(w_or_1()),
  prooftree(w_or_2()),
  prooftree(w_and()),
  prooftree(w_tuple()),
))

#rule_w

RULES FOR $t ~> w$ :

#let t_base(Delta: $Delta$, typ: $b$, wit: $w$, con: $c$) = rule(
  name: [Base],
  [$wit=con lt.eq.slant typ$],
  [$Delta |-""_s typ ~> wit$],
)

#let t_arrow(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$, wit1: $w_1$, wit2: $w_2$) = rule(
  name: [$->$],
  [$wit = wit1 -> wit2 lt.eq.slant typ1 -> typ2$],
  [$Delta |-""_s typ1 -> typ2 ~> wit$],
)

#let t_tuple(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit1: $w_1$, wit2: $w_2$) = rule(
  name: [$*$],
  [$Delta |-""_m typ1 ~> wit1$],
  [$Delta |-""_m typ2 ~> wit2$],
  [$Delta |-""_s typ1 * typ2 ~> wit1 * wit2$],
)

#let t_or_1(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$) = rule(
  name: [$or_1$],
  [$Delta |-""_m typ1 ~> wit$],
  [$Delta |-""_s typ1 or typ2 ~> wit$],
)

#let t_or_2(Delta: $Delta$, typ1: $t_1$, typ2: $t_2$, wit: $w$) = rule(
  name: [$or_2$],
  [$Delta |-""_m typ2 ~> wit$],
  [$Delta |-""_s typ1 or typ2 ~> wit$],
)

#let t_mem(Delta: $Delta$, typ: $t$, wit: $w$) = rule(
  name: [$typ in.not Delta$],
  [$Delta union {typ}|-""_s typ ~> wit$],
  [$Delta |-""_m typ ~> wit$],
)

#let rule_t = align(center, rule-set(
  prooftree(t_base()),
  prooftree(t_arrow()),
  prooftree(t_tuple()),
  prooftree(t_or_1()),
  prooftree(t_or_2()),
  prooftree(t_mem()),
))


#rule_t


Tree for $t = ("Int", ("Int" -> "Bool") or "Nil")$ :


#let exemple_t1 = prooftree(rule(
  name: $*$,
  rule(
    name: $"Int" in.not Delta$,
    t_base(Delta: $Delta = {"Int"}$, typ: "Int", wit: $w_1$, con: $42$),
    [$|-""_m "Int" ~> w_1$],
  ),
  rule(
    name: $t in.not Delta$,
    rule(
      name: $or_1$,
      rule(
        name: $"Int" -> "Bool" in.not Delta$,
        t_arrow(
          Delta: $Delta' = Delta union {"Int" -> "Bool"}$,
          typ1: "Int",
          typ2: "Bool",
          wit: $w_2$,
          wit1: "Int",
          wit2: BigZero,
        ),
        [$Delta |-""_m "Int" -> "Bool" ~> w_2$],
      ),
      [$Delta = {("Int" -> "Bool") or "Nil"))} |-""_s ("Int" -> "Bool") or "Nil") ~> w_2$],
    ),
    [$|-""_m t = ("Int" -> "Bool") or "Nil") ~> w_2$],
  ),
  [$|-""_s ("Int", ("Int" -> "Bool") or "Nil") ~> (w_1, w_2)$],
))

#exemple_t1

Tree for (42, Int -> O) : (Int, (Int -> Bool) or Nil)

#let exemple_w1 = prooftree(rule(
  name: $*$,
  w_base_case(typ: "Int", con: $42$),
  rule(
    name : $->$,
    [$"Int" -> BigZero lt.eq.slant ("Int" -> "Bool") or "Nil"$],
    [$|- "Int" -> BigZero : ("Int" -> "Bool") or "Nil"$],
  ),
  [$|- (42, "Int" -> BigZero) : ("Int", ("Int" -> "Bool") or "Nil")$],
))

#align(center, exemple_w1)


#let new_w_base(wit : $c$, typ : $b$) = rule(
  name : "Base",
  [$wit in [|typ|]$],
  [$wit : typ$]
)

#let new_w_arrow(wit1 : $w_1$, wit2 : $w_2$, typ1 : $t_1$, typ2 : $t_2$) = rule(
  name : $->$,
  [$wit1 -> wit2 lt.eq.slant typ1 -> typ2$],
  [$|- wit1 -> wit2 : typ1 -> typ2$])

#let new_w_tuple(wit1 : $w_1$, wit2 : $w_2$, typ1 : $t_1$, typ2 : $t_2$) = rule(
  name : $->$,
  [$|-wit1 : typ1$],
  [$|- wit2 : typ2$],
  [$|- (wit1 * wit2) : (typ1 * typ2)$])

#let new_rule_w = align(center, rule-set(
  prooftree(new_w_base()),
  prooftree(new_w_arrow()),
  prooftree(new_w_tuple())
))

#new_rule_w