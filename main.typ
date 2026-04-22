#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/tdtr:0.5.5": tidy-tree-graph


#import "macros.typ": *
#import "rules.typ": (
  exemple_t1, exemple_w1, exemple_w2, new_rule_w, new_w_arrow, new_w_base, new_w_tuple, rule_t, rule_w, t_arrow, t_base,
  t_mem, t_or_1, t_or_2, t_tuple,
)


#show: shorthands.with(($|-$, $tack.r$))

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

#outline(depth: 3)

= Introduction
Le but du stage a été de créer une fonction permettant, pour tout type non-vide, de trouver un habitant de ce type, appelé témoin. Ce témoin permet d'afficher un exemple lors de la diffusion d'un message d'erreur de mauvais typage.

==== Exemple
On a une fonction $f : Int -> Int$ et une variable $x : Int or Bool$. Alors l'application $f(x)$ est mal typée, car $Int or Bool lt.eq.not Int$. On cherche donc un témoin de $(Int or Bool) \\ Int = Bool$, ce qui peut rendre $True$ ou $False$. Pour des types plus complexes, on veut automatiser le processus, ce qui amène à l'algorithme "Witness" expliqué ici.
= Présentation des types ensemblistes REECRIRE
Les types utilisés dans ce rapport sont des types ensemblistes. On les définit comme :
$ t ::= b | alpha | t -> t | t times t | t or t | t and t | not t | BigZero | BigOne $
Où $b in BeauB$ sont les cas de bases (en particuliers les constances $c in BeauC$ ) et $alpha in nu$ les variables de types. $BeauB$ est composé de $Int$ (l'ensemble des entiers relatifs) et Enum (l'ensemble des types énumérés, par exemple bool).

Comme ces types sont définis co-inductivement, ils peuvent être définis comme des arbres infinis réguliers et contractifs. Un arbre est dit régulier si il a un nom fini de sous-termes possibles, et contractif si une branche infinie passe forcément par un constructeur (ici, $->$ et $times$).

==== Exemple de type t sous forme d'arbre
pour $t = Nil or (Int, t)$

#tidy-tree-graph(compact: false)[
  - $\_ or \_$
    - $Nil$
    - $(\_ , \_ )$
      - $Int$
      - $t$
]

On peut aussi représenter celà sous la forme d'un graphe cyclique en remplaçant la feuille $t$ par un flèche vers $\_or\_$. Ceci nous permet d'avoir une définition de type qui n'a pas besoin de définitions explicites pour la récursion.

Dans un premier temps, nous allons ignorer les variables de types pour la construction du témoin.

= Génération d'un témoin ECRIRE

== Définition d'un témoin

Un témoin est un habitant de notre type, c'est à dire une valeur constante apartenant à $[|t|]$. Dans le cas des flèches, on considère que l'on ne cherche pas à connaître plus que leur domaine (REECRIRE MIEUX).

On propose comme type témoin :
$ w ::= c | a | w times w $

En pratique, on a $c ::= i in [|Int|] | e in [|Enum|]$, EXPLICITER a !!!!! ainsi que des extensions pour les tags, les n-uplets et les records, ce qui donne :
$ w ::= i in [|Int|] | e in [|Enum|]| a | w times w times ... times w | "tag"(w) | {l_i : w ... l_n : w} $
Les tags, les n-uplets et les records ne sont en réalité que des cas particuliers des tuples, ils ne seront donc pas traités sur le plan théorique.

== Féfiniton de $w :t$

On peut donc définir un prédicat $w : t$ qui est vrai si et seulement si w est un témoin de t, avec les règles suivantes :

#new_rule_w

==== Exemple
On veut montrer que $w = (3, (True, Int -> Int))$ est bien un témoin de $t = (Int, (Bool, BigZero -> BigOne))$ :

#exemple_w2

= Présentation de l'algorithme

Notre algorithme respecte les règles d'inférences suivantes :

On peut ensuite décrire le fonctionnement de l'algorithme qui pour chaque type t associe un témoin w (qu'on notera $t ~> w$) qui a les règles suivantes :

#rule_t

==== Exemple :
On a $t = (Int, (Int -> Bool) or (Bool -> Int))$

Cela nous donne l'arbre :

#exemple_t1

On peut ainsi vérifier que $w = (42, Int -> BigZero)$ est bien un témoin de $t = (Int, (Int -> Bool) or (Bool -> Int))$ :

#align(center, exemple_w1)

= En Pratique
L'algorithme va essayer de trouver un témoin dans chacune des 6 grandes catégories (Int, Enum, Arrows, Tag, Tuple, Record) dans cet ordre, et s'arrêter dès qu'un est trouvé. Si aucun n'est trouvé, on considère le type comme vide et on lève une exception.
== Cas de bases

=== Int
Les entiers sont représentés comme des intervalles. Il existe 3 cas possibles :
- $t = ]-oo ; +oo[$ : l'algorithme retourne 42
- $t = ]-oo; i ] " " or " " [ i ; +oo[$ :  retourne $i$
- $t = [i_1; i_2]$ : retourne $i_1$

=== Enum
Enum contient tout les types énumérés, incluant notamment les booléens (et les Strings ?). Il peuvent être définis de 2 manières :
- comme une union des constantes appartenant à $t$ : on renvoie la première
- comme une union des constantes appartenant à $not t$ : On retourne une constante de Enum de taille n, n n'étant la taille d'aucune des constantes de $not t$

==== Exemples
+ Si $t = True | False$ alors $w = True$
+ Si $t = Enum \\ (a or "ba" or "toto")$ alors $w = "abc"$

=== Arrow
Etant donné qu'un type fonction est forcément habité, celà n'a pas de sens d'aller chercher un témoin dans chacune de ses branche, et peut même être contreproductif.
On va donc prendre tout les atomes positifs de t, et y rajouter un par un les atomes négatifs de t. Si au moment d'un ajout, l'intersection des atomes positifs et négatifs donne un sous-type de t, c'est notre témoin.


== Constructeurs

=== Tuple

Les n-uplets peuvent, comme les Enum, être défini comme les éléments présents dans $t$ ou comme les éléments présents dans $not t$.
- Si on a la liste des éléments présents dans $t$, on choisit l'élément e de plus petite arité dont aucun élément n'est vide, et on renvoie un n-uplet de la même taille  et dont chaque élément est le témoin du type à la même position dans e.
- Si on a la liste des éléments présents dans $not t$, on trouve le plus petit entier n tel qu'il n'y ai aucun n-uplet de cette arité dans la liste, et on en renvoie un témoin (usuellement le n-uplet (0,1,...,n))

==== Exemples
+ $t = (Int, Bool)$ donnera $w= (42, True)$
+ $t = Tuple \\ ((Int,) or (Int, Bool))$ donnera $w= (0,1,2)$

=== Tag

Les tags sont des tuples avec un type string en premier membre et un type t en deuxième. Ils servent à marquer certains types pour ne pas être confondus (ex : $"foo"(Int)$).
Ils sont traités de la même manière que les tuples de taille 2, à l'exception que l'on n'opère pas de récursion sur le premier membre.

==== Exemples
+ $t = "foo"(Int)$ donnera $w = "foo"(42)$
+ $t = Tag \\ "foo"(Int)$ donnera $w = "a"(16)$


= Preuve de sûreté
On veut montrer que le socle théorique de notre algorithme est fondé, nous allons donc montrer la terminaison de notre programme, ainsi que la preuve théorique de sa justesse.



== Preuve de la terminaison de $t ~> w$

On peut déjà noter que pour tout type t, $Delta$ a une taille maximale finie, car il est au maximum de la taille l'ensemble de tout les sous-types de t (qui sont, par définition de t, finis).

A chaque appel récursif, $Delta$ grandit, c'est donc une condition suffisante pour prouver la terminaison de l'algorithme. En pratique, ceci n'est utilisé que pour traiter les cas récursifs, nous proposons donc une preuve alternative pour les autres cas.


En peut aussi dire qu'en pratique, nos types sont stockés sous la forme de DNF, on a donc :

$ t = or.big (and.big b) or.big (and.big t_1 -> t_2) or.big (and.big (t_1 times t_2)) $

On a aussi un résultat qui dit que $forall t , t lt.eq.slant BigOne times BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$



Or $(t_1 times t_2) and (t_3 times t_4) = (t_1 and t_3 times t_2 and t_4)$, donc $and.big (t_1 times t_2) = (and.big t_1 times and.big t_2) lt.eq.slant BigOne times BigOne$, donc $and.big (t_1 times t_2) = or.big (t'_1, t'_2)$

Il suffit donc de montrer que $t ~> w$ termine si $t = b$, $t = t_1 -> t_2$, $t=t_1 times t_2$ et $t = t_1 or t_2$

Si $t = b$, alors il suffit de prendre un atome de b, ce qui se fait en temps fini.

Si $t= t_1 -> t_2$, alors $t_1 -> t_2$ est une solution, donc cela se fait aussi en temps fini.

Supposons maintenant que $t_1 ~> w_1$ et $t_2 ~> w_2$ finissent.

Si $t = t_1 times t_2$, alors par $times_t$, $t_1 times t_2 ~> w_1 times w_2$ termine si $t_1 ~> w_1$ et $t_2 ~> w_2$ terminent, ce qui est le cas par hypothèse. Donc $t_1 times t_2 ~> w_1 times w_2$ termine.

Si $t = t_1 or t_2$, alors :
- Par $or_1_t$, $t_1 or t_2 ~> w$ termine si $t_1 ~> w$ termine, ce qui est le cas par hypothèse
- Par $or_2_t$, $t_1 or t_2 ~> w$ termine si $t_2 ~> w$ termine, ce qui est le cas par hypothèse.
Donc si $t = t_1 or t_2$, alors $t ~> w$ termine.

Donc par induction, pour tout type t, $t ~> w$ termine.


== Preuve que si $emptyset |-""_m t ~> w$ alors $w:t$

Montrons par récurrence que $"Si" emptyset |-""_s t ~> w "alors" w:t$ :

Si $b ~> w$, alors par "Base", $w = c lt.eq.slant b$, donc $w = c in [|b|]$, donc $w:b$.

Si $t_1 -> t_2 ~> w$, alors par $->$, $w = w_1 -> w_2 lt.eq.slant t_1 -> t_2$ , donc par $->_w$, $w_1 -> w_2 : t_1 -> t_2$

Supposons par induction que $P(t_1,w_1)$ et $P(t_2,w_2)$ et montrons que $P(t_1 times t_2, w_1 times w_2)$. Si $(t_1 times t_2) ~> (w_1 times w_2)$, alors par $times_t$, $t_1 ~> w_1$ et $t_2 ~> w_2$, donc par hypothèse, $w_1 :t_1$ et $w_2 :t_2$, donc par $times_w$, $(w_1 times w_2) : (t_1 times t_2)$

Supposons par induction que  $P(t_1,w)$ et $P(t_2,w)$ et montrons que $P(t_1 or t_2, w)$. Si $t_1 or t_2 ~> w$, alors par $or_1_t$, $t_1 ~> w$, donc $w:t_1$, donc par ?????????

Donc pour tout type t, $"Si" emptyset |-""_m t ~> w "alors" w:t$
