#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/tdtr:0.5.5": tidy-tree-graph
#import "@preview/thmbox:0.3.0": *
#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#import "@preview/lovelace:0.3.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node


#import "macros.typ": *
#import "rules.typ": *
#import "algos.typ": *


#show: shorthands.with(
  ($|-m$, $attach(tack.r, br: m)$),
  ($|-s$, $attach(tack.r, br: s)$),
  ($|-a$, $attach(tack.r, br: a)$),
  ($|-$, $tack.r$),
  ($~=$, $tilde.eq$),
)
#let beth = strong([$beth$])


#show: arkheion.with(
  title: "Rapport de stage",
  authors: (
    (name: "Fred Belanger", email: "felix.belanger@universite-paris-saclay.fr", affiliation: ""),
  ),
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  date: "16 Avril 2026",
)
#set cite(style: "chicago-author-date")
#show link: underline
#show: thmbox-init()


#outline(depth: 3)

= Introduction
Le but du stage a été de créer une fonction permettant, pour tout type non-vide, de trouver un habitant de ce type, appelé témoin. Ce témoin permet d'afficher un exemple lors de la diffusion d'un message d'erreur pour mauvais typage.

#example()[
  On a une fonction $f : Int -> Int$ et une variable $x : Int or Bool$. Alors l'application $f(x)$ est mal typée, car $Int or Bool "n'est pas un sous-type de" Int$. On cherche donc un témoin de $(Int or Bool) \\ Int = Bool$, ce qui peut rendre $True$ ou $False$.
]
Pour des types plus complexes, on veut automatiser le processus, ce qui amène à l'algorithme "Witness" expliqué ici.

= Présentation des types ensemblistes

== Définition d'un type ensembliste

Les types utilisés dans ce rapport ont été introduits par M. Laurent, K. Nguyen et G. Castagna dans "A Gentle Introduction to Semantic Subtyping" @Cas05b et "Implementing Set-Theoretic Types" @laurent:hal-05369012 comme des types ensemblistes. On les définit comme :
$ t ::= b | alpha | t -> t | t times t | t or t | t and t | not t | BigZero | BigOne $
Où $b in BeauB$ sont les cas de bases (en particuliers les constantes $c in BeauC$ ), $alpha in BeauV$ les variables de types, $BigZero$ le type vide et $BigOne$ le supertype de tout les types.

#example()[
  $t = (Int, (True -> False)) or 42$ est un type correct dans notre syntaxe.
]
On définit $[|t|]$ comme l'ensemble des valeurs contenues dans t, ce qui nous permet de définir aussi la relation de sous-typage $t_1 lt.eq.slant t_2$ qui est vrai si et seulement si $[|t_1|] in [|t_2|]$. On peut noter qu'il existe des cas, comme $Bool$ et $Int$, où $Bool lt.eq.not Int$ et $Int lt.eq.not Bool$. On a aussi que $forall t, BigZero lt.eq.slant t lt.eq.slant BigOne$. On peut enfin définir l'égalité sémantique $t_1 ~= t_2$ comme étant vrai si et seulement si $t_1 lt.eq.slant t_2$ et $t_2 lt.eq.slant t_1$.

Comme ces types sont définis co-inductivement, ils peuvent être définis comme des arbres infinis réguliers et contractifs.

#definition()[
  Un arbre est dit *régulier* si il a un nom fini de sous-termes possibles.
]<regulier>

#definition()[
  Un arbre est dit *contractif* si une branche infinie passe forcément par un constructeur (ici, $->$ et $times$).
]<contractif>

#example()[
  $t = Nil or (Int times t)$ sous forme d'arbre:

  #tidy-tree-graph(compact: false)[
    - $\_ or \_$
      - $Nil$
      - $\_ times \_$
        - $Int$
        - $t$
  ]
]

On peut aussi représenter cela sous la forme d'un graphe cyclique en remplaçant la feuille $t$ par une flèche vers $\_or\_$. Ceci nous permet d'avoir une définition de type qui n'a pas besoin de définitions explicites pour la récursion.

Enfin, on considère les types infinis comme vides, car ils sont inconstructibles en pratique (ex : $t = (Int, t) lt.eq.slant BigZero$ ).

Dans un premier temps, nous allons ignorer les variables de type, nous y reviendront au chapitre 7.


#definition()[
  D'après la Définition C.13 de "Polymorphic Functions with set-theoretic types" @castagna:hal-00880744, un socle $beth$ $subset \u{1D4AF}$ est un ensemble de types avec les propriétés suivantes :
  - $beth$ est fini,
  - $beth$ est clos sous les connecteurs booléens ($or, and "et" not$).
  - Si $t_1 times t_2 in beth$ ou $t_1 -> t_2 in beth$ alors $t_1 in beth$ et $t_2 in beth$.
  De plus, si on a $S : {s | subset.eq.sq t}$ l'ensemble des sous-arbres de $t$, alors $exists beth$ tel que $S subset.eq beth$.]

Cette définition nous sera utile plus tard, lors de la création de l'algorithme de génération du témoin.

== Existence d'une forme normale disjonctive

En pratique, un type est toujours encodé sous la forme d'une DNF (forme normale disjonctive) :
$
  t ::= or.big_i b_i or or.big_i ( and.big_j (p_1^(i j) -> p_2^(i j)) and and.big_j not(n_1^(i j) -> n_2^(i j))) or or.big_i ( and.big_j (p_1^(i j) times p_2^(i j)) and and.big_j not(n_1^(i j) times n_2^(i j)))
$

Avec des atomes positifs, nommés p, et des atomes négatifs, nommés n. On notera que, dû à la récursivité de notre définition, on peut avoir des opérateurs d'union sous les opérateurs d'intersection (si on développe les types flèches et tuples). On appellera quand même cette forme une DNF par la suite, par mesure de simplicité. Les atomes de bases ne sont représentés que comme des unions car il sont très simplement simplifiables.

On peut simplifier cette définition en transformant la partie sur les tuples en une union d'unions :
#lemma(variant: "Lemme")[
  $forall t , t lt.eq.slant BigOne times BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$
]<lemma-one>

#proof[
  Si $t lt.eq.slant BigOne times BigOne$ alors :

  $t &= or.big (and.big_i (p_1^i, p_2^i)and and.big_j not(n_1^j, n_2^j))\
  &= or.big ((and.big_i (p_1^i, p_2^i))\\ or.big_j (n_1^j, n_2^j))\
  &= or.big ((and_i p_1^i,and_i p_2^i)\\ or.big_j (n_1^j, n_2^j))$ par commutativité de $and$

  Montrons par récurrence sur $or.big_j (n_1^j, n_2^j)$ que t est bien une union :

  On a bien $(and_i p_1^i,and_i p_2^i)$ qui est une union d'un seul élément.

  On a maintenant $or.big_i (t_1^i,t_2^i)$ une union, montrons que $or.big_i (t_1^i,t_2^i) \\ (n_1,n_2)$ est une union :
  $or.big_i (t_1^i,t_2^i) \\ (n_1,n_2) & = or.big_i ((t_1^i,t_2^i) \\ (n_1,n_2)) \
  &= or.big_i ((t_1^i \\ n_1,t_2^i) or (t_1^i,t_2^i \\ n_2))$ qui est une union.

  Donc par récurrence, $forall t , t lt.eq.slant BigOne times BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$.
]

\
Ainsi, on peut réécrire la définition vu plus haut :
$
  t ::= or.big_i b_i or or.big_i ( and.big_j (p_1^(i j) -> p_2^(i j)) and and.big_j not(n_1^(i j) -> n_2^(i j))) or or.big_i (t_1^i times t_2^i)
$


= Génération d'un témoin

== Définition d'un témoin

Un témoin est un habitant de notre type, c'est à dire une valeur constante appartenant à $[|t|]$. Notre but est, pour chaque cas de base, de trouver un habitant de ce cas, et pour chaque constructeur, de chercher récursivement un témoin pour chacune de ses parties.

#example()[
  16 est un témoin de $Int or Bool$.
]
Pour trouver un habitant d'une fonction $f$ de type $t_1 -> t_2$, il faut un langage qui puisse prendre un habitant de $t_1$ et renvoyer le résultat de $f("Witness"(t_1)) = "Witness"(t_2)$.  On pourrait utiliser des $lambda$ termes mais cela serait complexes pour les types récursifs. Enfin, savoir que $42 -> 43$ est un habitant de $Any -> Int$ ne nous aide pas vraiment. Le procédé est donc complexe est contre-productif, nous avons donc choisis de considérer les types flèches (de la forme $or.big_i ( and.big_j p_1^(i j) -> p_2^(i j) and and.big_j not(n_1^(i j) -> n_2^(i j)))$) comme des cas de base. On notera
$ A ::= and.big_i (p_1^i -> p_2^i) and and.big_j not(n_1^j -> n_2^j) $

Cela va nous permettre de réécrire une nouvelle fois notre définition de type :

$ t ::= or.big_i b_i or or.big_i A_i or or.big_i (t_1^i times t_2^i) $

Un témoin est donc soit une constante d'un cas de base, soit un type flèche, soit un tuple.
On propose donc comme type témoin :
$ w ::= c | A | (w,w) $<witness>


#example()[
  $w = (42, (True, False))$ est un témoin correct dans notre syntaxe.
]
== Définition de type_of(w) et $w >> t$

On peut donc créer l'algorithme type_of(w) qui pour tout témoin w renvoie le type t contenant uniquement w :

#rule_to_ty

On peut étendre cet algorithme afin que pour tout témoin w, il renvoie le type t tel que $w lt.eq.slant t$. On l'appellera $w >> t$ et aura les règles suivantes :

#rule_w

#example()[
  On veut montrer que $w = (3, (True, Int -> Int))$ est bien un témoin de $t = (Int, (Bool, BigZero -> BigOne))$ :

  #align(center, exemple_w2)
]
= Algorithme

== Présentation de l'algorithme

On peut maintenant décrire le fonctionnement de l'algorithme qui pour chaque type t associe un témoin w (qu'on notera $t ~> w$ et appellera Witness(t)) qui a les règles suivantes :

#rule_t

Ici, $Delta$ est l'ensemble des types déjà visité par l'algorithme. Ainsi, si l'on retombe sur le même type, on sait que celui-ci est infini, donc vide (comme expliqué ici *RAJOUTER LIEN*). On interdit donc de repasser plusieurs par un type déjà visité avec la règle $t in.not Delta$.

#example()[ :
  On a $t = Int times ((Int -> Bool) or Nil)$

  Cela nous donne l'arbre :

  #align(center, exemple_t1)

  On peut ainsi vérifier que $w = (42, Int -> BigZero)$ est bien un témoin de $t = Int times ((Int -> Bool) or Nil)$ :

  #align(center, exemple_w1)
]
== Preuve de terminaison de l'algorithme

#theorem()[
  Pour tout type $t$ non-vide, $t ~> w$ termine.
]<terminaison>

#proof()[
  On a, par définition, que $Delta subset.eq beth$, donc $Delta$ est de taille finie. On pose $u$ le nombre d'unions directes dans notre terme, avec $u =1$ si l'on choisit le membre de gauche, et $u = u-1$ si l'on choisit le membre de droite, et $s ::= cases(1 "si" |-s, 0 "si" |-m).$\
  Alors on peut construire le nombre $(beth \\ Delta|,u,s)$ Montrons que, quelque que soit la règle suivie, ce nombre décroît sur l'ordre lexicographique, assurant donc la terminaison de l'algorithme :

  Pour $"Base"_t$ : il suffit de prendre un atome de $or.big_i b_i$, ce qui se fait en temps fini.

  Pour $->_t$ : il suffit de prendre un atome de $A$, ce qui se fait aussi en temps fini.

  Pour $times_t$ : $s$ passe de 1 à 0 car on passe d'une règle $|-s$ à des règles $|-m$, on a donc bien  $(|beth \\ Delta|,u,0) lt_("lex") (|beth \\ Delta|,u,1)$.

  Pour $or_1_t$ : $u$ passe à 1, donc on a bien $(|beth \\ Delta|,1,1) lt_("lex") (|beth \\ Delta| ,u,1)$.

  Pour $or_2_t$ : $u$ passe à $u - 1$, donc on a bien $(|beth \\ Delta|,u - 1,1) lt_("lex") (|beth \\ Delta|,u,1)$.

  Pour $t in.not Delta$ : $u$ est susceptible d'augmenter, mais $Delta$ augmente, donc $|beth \\ Delta|$ décroît de 1,on a donc bien $(|beth \\ Delta| -1,u',1) lt_("lex") (|beth \\ Delta|,u,0)$.

  Donc par induction fondée sur l'ordre lexicographique de $(|beth \\ Delta|,u,s)$, pour tout type $t lt.eq.not BigZero, t~> w$ termine.
]

== Preuve de sûreté

#theorem()[
  Pour tout type $t$ non-vide, $"si" emptyset |-s t ~> w "alors" w >> t$.
  En d'autres termes, $forall t lt.eq.not BigZero, "type_of"("Witness"(t)) lt.eq.slant t$.
]<surete>

#proof()[
  On veut prouver $P(t) ::= "Si" emptyset |-s t ~> w "alors" w >> t$ :\
  On prouve par induction sur les règles d'inférences de $t ~> w$ :

  Pour $"Base"_t$ : Supposons $|-s b ~> w$, alors par $"Base"_t$, $w = c lt.eq.slant b$, donc $w = c in [|b|]$, donc $w >> b$.

  Pour $->_t$ : Supposons $|-s A ~> w$, alors par $->_t$, $w = w_1 -> w_2 lt.eq.slant A$ , donc par $->_w$, $w >> A$.

  Supposons maintenant $P(t_1)$ et $P(t_2)$.

  Pour $times_t$ : Supposons $(t_1 times t_2) ~> (w_1 , w_2)$, alors par $times_t$, $t_1 ~> w_1$ et $t_2 ~> w_2$, donc par $P(t_1)$ et $P(t_2)$, on a $w_1 >> t_1$ et $w_2 >> t_2$, donc par $times_w$, $(w_1 , w_2) >>(t_1 times t_2)$.

  Pour $or_1_t$ : Supposons $t_1 or t_2 ~> w$, alors par $or_1_t$, $t_1 ~> w$, donc par $P(t_1)$ on a $w >> t_1$, or $t_1 lt.eq.slant t_1 or t_2$ donc par $"Sous-type"_w$, $w >> t_1 or t_2$.

  Pour $or_2_t$ : Supposons $t_1 or t_2 ~> w$, alors par $or_2_t$, $t_2 ~> w$, donc par $P(t_2)$ on a $w >> t_2$, or $t_1 lt.eq.slant t_1 or t_2$ donc par $"Sous-type"_w$, $w >> t_1 or t_2$.

  Donc pour tout type $t$ non-vide, $"si" emptyset |-m t ~> w "alors" w >> t$.
]

= Extensions

Des extensions ont été rajoutés aux types ensemblistes déjà présents afin de couvrir certaines types précis : les n-uplets, les tags et les records. Ceux-ci ne sont que des versions spécifiques des tuples, ils ne seront donc pas traités sur le plan théorique. De plus, nos cas de bases peuvent être de 2 types : Int et Enum. On peut donc étendre notre définition de témoin :
$ w ::= i in [|Int|] | e in [|Enum|]| A | (w, w , ... , w) | "tag"(w) | {l_i : w ... l_n : w} $

== Tags
Les atomes de tags sont des tuples avec un type Tag (équivalent à un type string) en premier membre et un type $t$ en deuxième. Ils servent à marquer certains types pour ne pas être confondus (ex : $"foo"(Int)$).

== Records
Les atomes de records sont de la forme $ r ::= {"bindings" : ("Label" times f) "map"; "tail" : f; "exists" : ("Label Set" times f ) "Map"} $
- Ici, le type $f$ est une extension de notre type $t$ qui inclus les types optionnels (ex : $f = Int?$). On le définit comme $f in BigOne union bot$, $bot$ dénotant le type absent.
- Le bindings est un champ où l'on place toutes les variables nommées de notre record.
#example()[
  ${x : Int; y : Int?; "prédicat" : Bool}$
]
- La tail $f'$ indique si notre record est ouvert ou fermé (donc s'il peut avoir des variables supplémentaires non nommées).
#example()[
  ${x : Int;" " y : Int;;" " Int?}$ pour un système de coordonnées à au moins 2 dimensions.
]
- Pour chaque paire $(L_i : e_i)$ de exists, $L_i$ indique les noms que la variables ne peut PAS prendre et $e_i and f'$ indique son type.
#example()[
  ${x : Int; y : Int;; Any?;; {w;z} : Bool?}$ pour indiquer que les variables $w$ et $z$ ne peuvent pas avoir le type $Bool$ si elles existent.
]
= Implémentation

L'algorithme va essayer de trouver un témoin dans chacune des 6 grandes catégories (Int, Enum, Arrows, Tag, Tuple, Record) dans cet ordre, et s'arrêter dès qu'un est trouvé. Si aucun témoin n'est trouvé, on considère le type comme vide et on lève une exception.
== Cas de bases

=== Int
Les entiers sont représentés comme des intervalles. Il existe 3 cas possibles :
- $t = ]-oo ; +oo[$ : l'algorithme retourne 42.
- $t = ]-oo; i ]$ ou $t = [ i ; +oo[$ :  retourne $i$.
- $t = [i_1; i_2]$ : retourne $i_1$.

=== Enum
Enum contient tout les types énumérés, incluant notamment les booléens et les chaines de caractères. Il peuvent être définis de 2 manières :
- comme une union des constantes appartenant à $t$ : on renvoie la première
- comme une union des constantes appartenant à $not t$ : On retourne une constante de Enum de taille n, n n'étant la taille d'aucune des constantes de $not t$

==== Exemples
+ $True | False$ donnera $True$.
+ $Enum \\ (a or "ba" or "toto")$ donnera $"abc"$.

=== Arrow
Comme dit plus haut, on considère les atomes de la forme $and.big_i (t_1^i -> t_2^i) and and.big_j not(t_1 -> t_2)$ comme des cas de base.
On va donc prendre tout les atomes positifs de t, et y rajouter un par un les atomes négatifs de t. Si au moment d'un ajout, l'intersection des atomes positifs et négatifs donne un sous-type de t, c'est notre témoin.


== Constructeurs

=== N-uplets

Les n-uplets peuvent, comme les Enum, être défini comme les éléments présents dans $t$ ou comme les éléments présents dans $not t$.
- Si on a la liste des éléments présents dans $t$, on choisit l'élément e de plus petite arité dont aucun élément n'est vide, et on renvoie un n-uplet de la même taille  et dont chaque élément est le témoin du type à la même position dans e.
- Si on a la liste des éléments présents dans $not t$, on trouve le plus petit entier n tel qu'il n'y ai aucun n-uplet de cette arité dans la liste, et on en renvoie un témoin (usuellement le n-uplet (0,1,...,n))

==== Exemples
+ $(Int, Bool)$ donnera $(42, True)$
+ $Tuple \\ ((Int,) or (Int, Bool))$ donnera $(0,1,2)$

=== Tags

Les Tags sont traités de la même manière que les n-uplets de taille 2, à l'exception que l'on n'opère pas de récursion sur le premier membre.

==== Exemples
+ $"foo"(Int)$ donnera $"foo"(42)$.
+ $Tag \\ "foo"(Int)$ donnera $"a"(16)$.

=== Records

Pour générer un témoin, on va trouver un atome non vide de notre record, et opérer comme suit :

- Pour chaque paire $(l_i : f_i)$ de bindings, si $f_i$ est requis, alors on cherche récursivement un témoin $w_i$ de $f_i$ et ajouter $(l_i : w_i)$ au bindings de notre témoin $w$.\
#example()[
  ${x : Int; y : Int?; "prédicat" : Bool}$ donnera ${x : 42; "prédicat" : True}$.
]
- Si la tail $f'$ est requise, on l'ajoute dans la tail de $w$.
==== Exemples
+ ${x : Int;;" " Bool}$ donnera ${x: 42;; True}$.\
+ ${x : Int;;" " Bool?}$ donnera ${x :42}$.
- Pour chaque paire $(L_i : e_i)$ de exists, si $e_i and f$ est requis, alors on crée un label $l'_i in.not L_i$, on cherche récursivement un témoin $w'_i$ de $e_i and f$ et on ajoute $(l'_i : w'_i)$ *au bindings*.
#example()[
  ${x : Int; y : Int "";;"" Any? "" ;; "" {w;z} : Bool}$ donnera ${x : 42 "" ; "" y : 42 "" ; "" a : True}$
]


= Variables de type

== Définition
On veut maintenant intégrer les variables de type (aussi appelés types polymorphes) dans notre recherche de témoin. On commence donc par étendre notre définition de t :

$ t ::= b | alpha | t -> t | t times t | t or t | t and t | not t | BigZero | BigOne $


#definition()[
  Un type $t$ est *non-vide* si et seulement si il existe une substitution $sigma$ tel que $t sigma lt.eq.not BigZero$.
]

On veut donc renvoyer une substitution $sigma$ et un témoin de $t sigma$, avec comme conditions que Vars($t sigma$) = $emptyset$, $t sigma lt.eq.not BigZero$ et Witness($t sigma$) $>> t sigma$.

Notre témoin ressemblera donc à :
$ w' ::= (sigma, w) $
Avec $sigma$ l'ensemble des substitutions et w le témoin présenté à l'@witness.

#definition()[
  Le *tallying* (noté $Tally(s_1, t_1)=[[(alpha¹, sigma_1 (alpha¹)),...,(alpha^k, sigma_1 (alpha^k))],...,[(alpha¹, sigma_n (alpha¹)), ... , (alpha^k, sigma_n (alpha^k) ) ] ]$ ) est un algorithme qui renvoie toutes les substitutions $sigma$ tel que $forall sigma_i in sigma, forall j lt.eq n, s_j sigma_i lt.eq.slant t_j.$ Toutes les substitutions sont de la forme ${alpha |-> (alpha or t_inf) and t_sup}$ afin de borner efficacement l'algorithme.
]
#example()[

  $Tally((alpha, beta), BigZero)&= [ [(alpha, BigZero), (beta, beta)],\
    &"  " [(alpha, alpha), (beta, BigZero)]]\
  &=[[{alpha |-> (BigZero or alpha) and BigZero}, {beta |-> (BigZero or beta) and BigOne}],\
    & "  " [{alpha |-> (BigZero or alpha) and BigOne}, {beta |-> (BigZero or beta) and BigZero}]]$
]
#note()[
  Les variables de types ont un ordre total $prec.eq$. Ainsi, une variable $alpha^i$ ne peut pas avoir dans sa substitution les variables $alpha^1,...,alpha^(i-1)$, i.e $forall i,j , forall k < i, alpha^k in.not Vars(sigma_j (alpha^i))$
]

#note()[
  L'algorithme de Tallying renvoie une réponse complète, c'est-à-dire qu'il n'existe pas de substitutions qui ne soient pas des sous-cas d'une des solutions et qui soit une solution au problème de tallying.
]


#example()[

  $Tally(alpha\\ beta, BigZero) &= [[(alpha, alpha and beta),(beta, beta)]]\
  &= [[{alpha |-> (BigZero or alpha) and beta}, {beta |-> (BigZero or beta) and BigOne}]]$
]
#definition()[
  On dit qu'une substitution $sigma_j$ est *débornée* pour une variable $alpha^i$ si on a $inf_j^i lt.eq.slant BigZero$ et $sup_j^i gt.eq.slant BigOne$. Cela veut dire que cette variable ne joue pas de rôle dans la substitution.
]

En pratique on va représenter le tallying sous la forme d'un tableau :

#grid(
  columns: 5,
  rows: 5,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [tally], [$alpha^1$], [$alpha^2$], [...], [$alpha^k$],
  [$sigma_1$], [$i^1_1, s^1_1$], [$i^2_1, s^2_1$], [...], [$i^k_1,s^k_1$],
  [$sigma_2$], [$i^1_2, s^1_2$], [$i^2_2, s^2_2$], [...], [$i^k_2,s^k_2$],
  [...], [...], [...], [...], [...],
  [$sigma_n$], [$i^1_n, s^1_n$], [$i^2_n, s^2_n$], [...], [$i^k_n,s^k_n$],
)
avec $i^i_j "et" s^i_j$ respectivement les bornes inférieures et supérieures de $sigma_j (alpha^i)$.

#lemma()[
  Toutes les substitutions de $Tally(t, BigZero)$ avec t non vide *sont bornées sur au moins une variable*. Sinon, elle serait équivalente à la substitution identité ${}$, donc $t{} lt.eq.slant BigZero$, donc t serait vide.
]

#example()[

  Pour $Tally[((alpha, not alpha), BigZero)]$ :

  #grid(

    columns: 3,
    rows: 3,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha$], [$beta$],
    [$sigma_1$], [$BigZero, BigZero$], [$BigZero, BigOne$],
    [$sigma_2$], [$BigZero, BigOne$], [$BigZero, BigZero$],
  )

  Pour $Tally[(alpha \\ beta, BigZero)]$ :

  #grid(

    columns: 3,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha$], [$beta$],
    [$sigma_1$], [$BigZero, beta$], [$BigZero, BigOne$],
  )
]
== Présentation de l'algorithme

On cherche à trouver la substitution $sigma$ tel que $Vars(t) = emptyset$ et $t sigma lt.eq.not BigZero$. On appelle cet algorithme $polyw(t)$.

On distingue 3 cas possibles :
- Si $Vars(t) = emptyset$, on renvoie la substitution identité.
- Si $Tally[(t, BigZero)] = emptyset$, le type n'a aucune substitution qui puisse le vider, on substitue donc toutes les variables par un type arbitraire sans variable (ici $BigZero$) : $union.big_(alpha^i in Vars(t)) {alpha^i -> BigZero}$.
- Sinon, on crée la substitution $sigma := {alpha^k -> nu}$ avec $alpha^k$ et $nu$ choisis correctement (et expliqués plus loin), et on renvoie $sigma union polyw(t sigma).$

Pour choisir correctement $alpha^k$ et $nu$ dans le dernier cas, on va donc utiliser le tallying, afin de déterminer quelle substitution ne vide *pas* notre type t.\

On commence par choisir $alpha^k$ tel que celle-ci soit la plus grande variable de $Vars(t)$ selon l'ordre total $prec.eq$. Notre substitution sera donc de la forme $sigma := {alpha^k -> nu}$. \

=== Création du tableau de contraintes

Une fois cela fait, on va créer un tableau contenant toutes les bornes dans lesquelles on ne veut *pas* que $nu$ soit, et ceci en 2 étapes :

==== Colonne de $alpha^k$

On va d'abord prendre la colonne $alpha^k$ dans le tableau du tallying :

#grid(
  columns: 2,
  rows: 5,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^k$],
  [$sigma_1$], [$i^k_1,s^k_1$],
  [$sigma_2$], [$i^k_2,s^k_2$],
  [...], [...],
  [$sigma_n$], [$i^k_n,s^k_n$],
)
Puis supprimer les substitutions débornées, car alors la variable $alpha^k$ n'influe pas sur la substitution.

#example()[
  Pour $(alpha^1, not alpha^1) \\ (alpha², Int)$ : \
  $Tally[((alpha^1, not alpha^1) \\ (alpha², Int), BigZero)] =$

  #grid(

    columns: 3,
    rows: 4,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha^1$], [$alpha^2$],
    [$sigma_1$], [$BigZero, BigZero$], [$BigZero, BigOne$],
    [$sigma_2$], [$BigOne, BigOne$], [$BigZero, BigOne$],
    [$sigma_3$], [$alpha^2 and Int, Int$], [$not Int, BigOne$],
  )

  On ne garde que la colonne $alpha^2$, et l'on supprime les cases débornées :

  #grid(
    columns: 2,
    rows: 2,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha^2$],
    [$sigma_1$], [$not Int, BigOne$],
  )
]
==== Ajout des substitutions liées

On veut maintenant prévenir le cas où substituer $alpha^k$ débornerai toutes les cases d'une ligne, et transformerai donc la ligne en la substitution identité, ce qui équivaut à créer le type vide. On cherche donc à ce que dans chaque ligne, après l'application de la substitution ${alpha^k -> nu}$, il existe au moins une case bornée.

Pour cela, nous allons uniquement nous intéresser aux lignes où $alpha^k$ apparaît dans une borne et où toutes les autres cases sont débornées. On choisit arbitrairement une borne dans laquelle $alpha^k$ apparaît, et :
- si c'est une borne inférieure $i^i_j$, on rajoute la colonne $alpha^k$ de $Tally[(i^i_j, BigZero)]$ à notre tableau de contrainte.
- Si c'est une borne supérieure $s^i_j$, on rajoute la colonne $alpha^k$ de $Tally[(BigOne, s^i_j)]$ à notre tableau de contrainte.

Comme $alpha^k$ est toujours le dernier élément de son ordre total, il n'y a pas de variable de type dans les substitutions.

#example()[
  Pour $alpha^1 \\ alpha^2$ : \
  $Tally[(alpha^1 \\ alpha^2, BigZero)] =$

  #grid(

    columns: 3,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha^1$], [$alpha^2$],
    [$sigma_1$], [$BigZero, alpha^2$], [$BigZero, BigOne$],
  )
  On garde uniquement la colonne $alpha^2$ avec les cases bornées (ici aucunes):

  #grid(

    columns: 1,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [$alpha^2$],
  )

  Pour chaque ligne, on vérifie si toutes les cases sont débornées ou contiennent $alpha^2$ dans leur bornes (ici, la ligne $sigma_1$) et on rajoute les tallying respectifs :

  $Tally[(BigOne, alpha^2)] =$
  #grid(

    columns: 2,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [], [$alpha^2$],
    [$sigma_1$], [$BigZero, BigOne$],
  )
  On rajoute donc la colonne $alpha^2$ à notre tableau de contraintes (en rouge) :

  #grid(

    columns: 1,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [$alpha^2$],
    [#text(fill: red)[$BigOne, BigOne$]],
  )
]

=== Créer $nu$ respectant ces contraintes

On veut donc que pour toute case (i,s) du tableau de contrainte, $i lt.eq.not nu or nu lt.eq.not s$.
Afin de mieux visualiser le problème, on peut voir notre système de type comme un treillis complet infini, et nos contraintes de types comme des chemins à "éviter" pour choisir un bon type :

#diagram(
  node-defocus: 0,
  spacing: (1cm, 2cm),
  edge-stroke: 1pt,
  crossing-thickness: 5,

  node((0, 0), $BigOne$),

  node((-1, 1), $Int or Enum$),
  node((0, 1), $Int or Tuple$),
  node((+1, 1), $Enum or Tuple$),

  node((-1, 2), $Int$),
  node((0, 2), $Enum$),
  node((+1, 2), $Tuple$),

  node((0, 3), $BigZero$),
  node((-0.25, 2.5), "..."),
  node((0.25, 2.5), "..."),
  node((-1, 2.5), $...$),
  node((1, 2.5), $...$),
  node((-1, 0.5), $...$),
  node((1, 0.5), $...$),

  {
    let quad(a, b, ..args) = {
      edge(a, b, "..", ..args)
    }

    quad((0, 0), (-1, 1))
    quad((0, 1), (-1, 2))
    quad((1, 2), (0, 3))

    quad((0, 0), (0, 1))
    quad((-1, 1), (-1, 2))
    quad((+1, 1), (+1, 2))
    quad((0, 2), (0, 3))

    quad((0, 0), (1, 1))
    quad((-1, 1), (0, 2), "crossing")

    quad((-1, 2), (0, 3))
    quad((0, 1), (+1, 2))

    quad((1, 1), (0, 2), "crossing")

    quad((0, 3), (0.25, 2.5))
    quad((0, 3), (-0.25, 2.5))

    quad((-1, 2), (-1, 2.5))
    quad((1, 2), (1, 2.5))
    quad((-1, 1), (-1, 0.5))
    quad((1, 1), (1, 0.5))
  },
)

Représentation des types ensemblistes sous forme de treillis. Tout les chemins ne sont pas représentés (car il y en a un nombre infini) et les chemins en pointillés indiquent qu'il peut y avoir d'autres types entre 2 types.

On peut donc representer nos contraintes comme l'ensemble de tout les chemins entre une paire (i,s) :


#diagram(
  axes: (ltr, btt),
  edge-stroke: 2pt,
  edge-corner-radius: 50pt,
  mark-scale: 50%,
  node-outset: 0pt,

  //(i1,s1)
  edge((0.5, 0.5), (0, 3), bend: 15deg),
  edge((0.5, 0.5), (0, 3), bend: -15deg),
  edge((0.5, 0.5), (0, 3), bend: 30deg),
  node((0.5, 0.5), $i^1_1$),
  node((0, 3), $s^1_1$),

  //(i2,s2)
  edge((1, 1), (2.5, 2.5), bend: -15deg),
  edge((1, 1), (2.5, 2.5), bend: -30deg),
  edge((1, 1), (2.5, 2.5), bend: 15deg),
  node((1, 1), $i^1_2$),
  node((2.5, 2.5), $s^1_2$),

  //(i3,s3)
  edge((0.5, 0), (1.75, 3), bend: -40deg),
  edge((0.5, 0), (1.75, 3), bend: 05deg),
  node((0.5, 0), $i^1_3$),
  node((1.75, 3), $s^1_3$),

  //edges from 0
  edge((1, -0.5), (0.5, 0.5), "..", stroke: 0.1em),
  edge((1, -0.5), (1, 1), "..", stroke: 0.1em),
  edge((1, -0.5), (0.5, 0), "..", stroke: 0.1em),
  /* edge((1,-0.5), (2.5,2.5), "..", stroke: 0.1em),
  edge((1,-0.5), (0,3), "..", stroke: 0.1em),
  edge((1,-0.5), (1.75,3), "..", stroke: 0.1em), */
  node((1, -0.5), $BigZero$),

  //edges to 1
  edge((2.5, 2.5), (1, 4), "..", stroke: 0.1em),
  edge((0, 3), (1, 4), "..", stroke: 0.1em),
  edge((1.75, 3), (1, 4), "..", stroke: 0.1em),
  node((1, 4), $BigOne$),
)

Créer un $nu$ respectant ces contraintes revient donc à trouver un point n'étant sur aucun chemin de contrainte.

#example()[
  On a le tableau de contrainte suivant :
  #grid(

    columns: 1,
    inset: (x: 15pt, y: 7pt),
    stroke: 1pt,
    [$alpha^1$],
    [$BigZero, Int$],
    [$Enum, BigOne$],
  )
  Alors le treillis ressemblera à ça :

  #diagram(
    node-defocus: 0,
    spacing: (1cm, 2cm),
    edge-stroke: 1pt,
    crossing-thickness: 5,

    node((0, 0), text(red, $BigOne$)),

    node((-1, 1), text(red, $Int or Enum$)),
    node((0, 1), $Int or Tuple$),
    node((+1, 1), text(red, $Enum or Tuple$)),

    node((-1, 2), text(red, $Int$)),
    node((0, 2), text(red, $Enum$)),
    node((+1, 2), $Tuple$),

    node((0, 3), text(red, $BigZero$)),
    node((-0.25, 2.5), "..."),
    node((0.25, 2.5), "..."),
    node((-1, 2.5), $...$),
    node((1, 2.5), $...$),
    node((-1, 0.5), $...$),
    node((1, 0.5), $...$),

    {
      let quad(a, b, ..args) = {
        edge(a, b, "..", ..args)
      }

      edge((0, 0), (-1, 1), stroke: red)
      quad((0, 1), (-1, 2))
      quad((1, 2), (0, 3))

      quad((0, 0), (0, 1))
      quad((-1, 1), (-1, 2))
      quad((+1, 1), (+1, 2))
      quad((0, 2), (0, 3))

      edge((0, 0), (1, 1), stroke: red)
      edge((-1, 1), (0, 2), "crossing", stroke: red)

      edge((-1, 2), (0, 3), stroke: red)
      quad((0, 1), (+1, 2))

      edge((1, 1), (0, 2), "crossing", stroke: red)

      quad((0, 3), (0.25, 2.5))
      quad((0, 3), (-0.25, 2.5))

      quad((-1, 2), (-1, 2.5))
      quad((1, 2), (1, 2.5))
      quad((-1, 1), (-1, 0.5))
      quad((1, 1), (1, 0.5))
    },
  )

  Donc des solutions comme \"a\", $Tuple$, $42 or (Int, Enum)$ sont des bons $nu$, mais $Enum or [0, +oo[$ ou $BigOne$ videraient le type.


]

Créer l'algorithme permettant de trouver ces types s'est avéré très compliqué, et celà n'a pas été fait dans le cadre de ce stage. Pour le reste du rapport, on considerera que l'on a un oracle $createnu("ts")$ qui prend en entrée un tableau ts correctement formé et renvoie en sortie $nu$ tel $forall (i,s) in "ts", i lt.eq.not nu or nu lt.eq.not s$.

//On va donc créer un algorithme, nommé $createnu$ tel que pour tout tableau de contrainte correctement formé $"ts"$, $createnu("ts")$ renvoie $nu$ tel que $forall (i,s) in "ts", i lt.eq.not nu or nu lt.eq.not s$.

#note()[
  On considère un tableau de contrainte comme *correctement formé* si un tel $nu$ existe, sinon cela voudrait dire qu'il n'existe aucun type $nu$ tel que $t[alpha^k <- nu] lt.eq.not BigZero$, ce qui est impossible.
]

#example()[
  En continuant l'exemple de $alpha^1 \\ alpha^2$, $createnu[(BigOne, BigOne)]$ renvoie $nu$ tel que $BigOne lt.eq.not nu or nu lt.eq.not BigOne <=> nu != BigOne$. Donc n'importe quel type qui ne soit pas $BigOne$ est une solution acceptable.
]



== Preuve de terminaison

#theorem()[
  Pour tout type non-vide, l'algorithme polyw termine en temps fini.
]

#proof()[
  On peut distinguer 3 cas possibles pour notre algorithme :
  - Si le type t n'a pas de variables de type : on renvoie la fonction identité, ce qui se fait en temps fini
  - Si $Tally[(t, BigZero)]= emptyset$ : On renvoie la substitution $union.big_(alpha^i in Vars(t)) {alpha^i -> BigZero}$, ce qui se fait aussi en temps fini
  - Sinon : \
  Créer le tableau de contrainte se fait en temps fini, et la trouver le $nu$ aussi. Comme il n'existait aucune variable de type dans les cases du tableau de contrainte, $nu$ n'en contient pas non plus, donc $Vars(t [alpha^k <- nu])$ contient strictement moins d'éléments que $Vars(t)$. Donc par un ordre numérique sur la taille de $Vars(t)$, notre algorithme termine bien.
]

== Preuves de sûretés

#theorem()[
  Pour tout type $t$ non-vide, $polyw(t)$ renvoie une substitution $sigma$ tel que $Vars(t sigma) = emptyset and t sigma lt.eq.not BigZero$.
]

#proof()[


  La terminaison de notre algorithme est fondée sur la diminution du nombre de variable de type, et nos 2 conditions d'arrêts s'assurent que $t sigma$ n'ait plus de variable de type, il est donc trivial de montrer que $polyw(t) = sigma$ renvoie bien une substitution telle que $Vars(t sigma) = emptyset$.

  Montrons maintenant que l'algorithme ne peux pas renvoyer une substitution qui vide le type t :

  Prouver que t ne deviens pas vide reviens à prouver qu’aucune ligne du tableau de tallying ai toutes ses cases débornées, on va donc séparer cela en plusieurs cas :

  *Si la case $alpha^k$ de la ligne est bornée : *
  Comme le choix de $nu$ s'assure que $alpha^k$ sera substitué par quelque chose en dehors de ses bornes, la ligne est supprimée, donc on ne peut plus produire un type vide avec cette substitution.

  *Si la case $alpha^k$ est débornée mais qu'aucune autre case de la ligne n'avait $alpha^k$ dans ses substitutions :*
  Il y avait forcément une autre case bornée dans la ligne, donc quelque soit le $nu$ choisi, la substitution ne devient pas l'identité.

  *Si la case $alpha^k$ est débornée, que $alpha^k$ apparaît dans les bornes d'une autre case mais qu'une case dont les bornes ne contiennent pas $alpha^k$ est bornée :*
  Même si le choix de $nu$ déborne d'autres cases, une case reste bornée, donc le type ne devient pas vide.

  *Si la case $alpha^k$ est débornée, qu'$alpha^k$ apparaît dans les bornes d'une autre case et que toutes les autres cases sont débornées :*
  Grâce à la partie du tableau de contrainte où l'on ajoute les contraintes des substitutions liées, le choix de $nu$ s'assure qu'au moins une case de la ligne ne soit pas débornée.

  Donc quelque soit la forme de notre ligne de substitution, notre $nu$ s'assure que la ligne soit supprimée où qu'elle ne soit pas entièrement débornée. Donc notre type ne peut pas devenir vide, donc pour tout type t non-vide, on a $sigma := polyw(t)$ tel que $t sigma lt.eq.not BigZero$.

]
= Un cas concret

Faisons un exemple complet avec $t = (alpha^1, not alpha^1) \\ (alpha^2, alpha^3)$ :

$Tally(t, BigZero) =$
#grid(

  columns: 4,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^1$], [$alpha^2$], [$alpha^3$],
  [$sigma_1$], [$BigZero, BigZero$], [$BigZero,BigOne$], [$BigZero,BigOne$],
  [$sigma_2$], [$BigOne,BigOne$], [$BigZero,BigOne$], [$BigZero,BigOne$],
  [$sigma_3$], [$not alpha^3, not alpha^3 or alpha^2$], [$not alpha^3, BigOne$], [$BigZero, BigOne$],
)
Donc notre tableau de contrainte ts est vide, car $alpha^3$ n'a que des cases débornées. $alpha^3$ apparaît dans $sigma_3$, et il n'y a pas de case bornée où $alpha^3$ n'apparait pas, \
donc on fait $Tally(not alpha^3, BigZero) =$
#grid(
  columns: 2,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^3$],
  [$sigma_1$], [$BigOne, BigOne$],
)
Donc on l'ajoute à ts :
#grid(
  columns: 1,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [$alpha^3$],
  [$BigOne, BigOne$],
)
$createnu("ts") = not 42$, donc on a la substitution ${alpha^3 -> not 42}$.\
$t [alpha^3 <- not 42] = (alpha^1, not alpha^1) \\ (alpha^2, not 42)$ , donc on recommence :
$Tally(t [alpha^3 <- not 42], BigZero) =$
#grid(

  columns: 3,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^1$], [$alpha^2$],
  [$sigma_1$], [$BigZero, BigZero$], [$BigZero,BigOne$],
  [$sigma_2$], [$BigOne,BigOne$], [$BigZero,BigOne$],
  [$sigma_3$], [$42, 42 or alpha^2$], [$42, BigOne$],
)
On crée le tableau de contrainte ts :
#grid(
  columns: 1,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [$alpha^2$],
  [$42, BigOne$],
)
Comme la case $sigma_3(alpha^2)$ est bornée, on a pas besoin de rajouter quoi que ce soit pour cette ligne.\
$createnu("ts") = 42$, donc on a la substitution ${alpha^2 -> BigZero}$.\
$t [alpha^3 <- not 42] [alpha^2 <- BigZero] = (alpha^1, not alpha^1)$, donc on recommence : $Tally((alpha^1, not alpha^1), BigZero) =$
#grid(

  columns: 2,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [], [$alpha^1$],
  [$sigma_1$], [$BigZero, BigZero$],
  [$sigma_2$], [$BigOne,BigOne$],
)

On crée le tableau de contrainte ts :
#grid(

  columns: 1,
  inset: (x: 15pt, y: 7pt),
  stroke: 1pt,
  [$alpha^1$],
  [$BigZero, BigZero$],
  [$BigOne,BigOne$],
)
$createnu("ts") = not 42$, donc on a la substitution ${alpha^1 -> not 42}$.
Donc on a $t [alpha^3 <- not 42] [alpha^2 <- BigZero] [alpha^1 <- not 42] = (not 42, 42)$, ce qui ne contient pas de variable de type, donc l'algorithme renvoit $sigma = {alpha^1 -> not 42; alpha^2 -> BigZero; alpha^3 -> not 42}$ et $t sigma = (not 42, 42)$.

On peut maintenant faire Witness$(not 42, 42)$ = (Witness$(not 42)$, Witness$(42)$) = (41,42).

Donc $t = (alpha^1, not alpha^1) \\ (alpha^2, alpha^3)$ a pour habitant (41,42) avec la substitution ${alpha^1 -> not 42; alpha^2 -> BigZero; alpha^3 -> not 42}$.



= Conclusion et perspectives

Au cours de ce stage, nous avons implémenté l'algorithme de witness pour les types monomorphes, prouvé sa sûreté, et avons grandement avancé sur l'algorithme permettant de retirer les variables de type d'un type polymorphe sans le rendre vide.

Une suite possible serait de trouver un algorithme implémentant $createnu("ts")$, afin de permettre une utilisation pratique de l'algorithme.


#pagebreak()

#bibliography("bibliography.bib", full: true)
