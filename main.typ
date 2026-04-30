#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/tdtr:0.5.5": tidy-tree-graph
#import "@preview/thmbox:0.3.0": *

#set text(lang: "fr")

#import "macros.typ": *
#import "rules.typ": *


#show :  shorthands.with(($|-$, $tack.r$), ($~=$, $tilde.eq$))
#show :  arkheion.with(
  title: "Rapport de stage",
  authors: (
    (name: "Fred Belanger", email: "felix.belanger@universite-paris-saclay.fr", affiliation: ""),
  ),
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: [On a fait des bêtises sur les problèmes de typage],
  date: "16 Avril 2026",
)
#set cite(style: "chicago-author-date")
#show link: underline
#show :  thmbox-init()

#outline(depth: 3)

= Introduction
Le but du stage a été de créer une fonction permettant, pour tout type non-vide, de trouver un habitant de ce type, appelé témoin. Ce témoin permet d'afficher un exemple lors de la diffusion d'un message d'erreur pour mauvais typage.

==== Exemple
On a une fonction $f : Int -> Int$ et une variable $x : Int or Bool$. Alors l'application $f(x)$ est mal typée, car $Int or Bool "n'est pas un sous-type de" Int$. On cherche donc un témoin de $(Int or Bool) \\ Int = Bool$, ce qui peut rendre $True$ ou $False$. Pour des types plus complexes, on veut automatiser le processus, ce qui amène à l'algorithme "Witness" expliqué ici.


= Présentation des types ensemblistes

== Définition d'un type ensembliste

Les types utilisés dans ce rapport ont été introduits par M. Laurent, K. Nguyen et G. Castagna dans "A Gentle Introduction to Semantic Subtyping" @Cas05b et "Implementing Set-Theoretic Types" @laurent:hal-05369012 comme des types ensemblistes. On les définit comme :
$ t ::= b | alpha | t -> t | t times t | t or t | t and t | not t | BigZero | BigOne $
Où $b in BeauB$ sont les cas de bases (en particuliers les constantes $c in BeauC$ ), $alpha in BeauV$ les variables de types, $BigZero$ le type vide et $BigOne$ le supertype de tout les types. $BeauB$ est composé de $Int$ (l'ensemble des entiers relatifs) et Enum (l'ensemble des types énumérés, par exemple bool).

==== Exemple :
$t = (Int, (True -> False)) or 42$ est un type correct dans notre syntaxe.

On définit $[|t|]$ comme l'ensemble des valeurs contenues dans t, ce qui nous permet de définir aussi la relation de sous-typage $t_1 lt.eq.slant t_2$ qui est vrai si et seulement si $[|t_1|] in [|t_2|]$. On peut noter qu'il existe des cas, comme $Bool$ et $Int$, où $Bool lt.eq.not Int$ et $Int lt.eq.not Bool$. On a aussi que $forall t, BigZero lt.eq.slant t lt.eq.slant BigOne$. On peut enfin définir l'égalité sémantique $t_1 ~= t_2$ comme étant vrai si et seulement si $t_1 lt.eq.slant t_2$ et $t_2 lt.eq.slant t_1$.

Comme ces types sont définis co-inductivement, ils peuvent être définis comme des arbres infinis réguliers et contractifs.

#definition()[
  Un arbre est dit *régulier* si il a un nom fini de sous-termes possibles.
]<regulier>

#definition()[
  Un arbre est dit *contractif* si une branche infinie passe forcément par un constructeur (ici, $->$ et $times$).
]<contractif>

==== Exemple
$t = Nil or (Int, t)$ sous forme d'arbre:

#tidy-tree-graph(compact: false)[
  - $\_ or \_$
    - $Nil$
    - $(\_ , \_ )$
      - $Int$
      - $t$
]

On peut aussi représenter cela sous la forme d'un graphe cyclique en remplaçant la feuille $t$ par une flèche vers $\_or\_$. Ceci nous permet d'avoir une définition de type qui n'a pas besoin de définitions explicites pour la récursion.

Enfin, on considère les types infinis comme vides, car ils sont inconstructibles en pratique (ex : $t = (Int, t) lt.eq.slant BigZero$ ).

Dans un premier temps, nous allons ignorer les variables de types pour la génération du témoin.


#definition()[
  D'après la Définition C.13 de "Polymorphic Functions with set-theoretic types" @castagna:hal-00880744, un socle *$beth$* $subset \u{1D4AF}$ est un ensemble de types avec les propriétés suivantes :
  - *$beth$* est fini, 
  - *$beth$* est clos sous les connecteurs booléens ($or, and "et" not$).
  - Si $t_1 times t_2 in $*$beth$* ou $t_1 -> t_2 in $*$beth$* alors $t_1 in $*$beth$* et $t_2 in $*$beth$*. 
  De plus, si on a $S : {s | subset.eq.sq t}$ l'ensemble des sous-arbres de $t$, alors $exists $*$beth$* tel que $S subset.eq $*$beth$*.]

Cette définition nous sera utile plus tard, lors de la création de l'algorithme de génération du témoin.

== Existence d'une forme normale disjonctive

En pratique, un type est toujours encodé sus la forme d'une DNF (forme normale disjonctive) :
$
  t ::= or.big_i b_i or or.big_i ( and.big_j p_1^(i j) -> p_2^(i j) and and.big_j not(n_1^(i j) -> n_2^(i j))) or or.big_i ( and.big_j (p_1^(i j) times p_2^(i j)) and and.big_j not(n_1^(i j) times n_2^(i j)))
$

Avec des atomes positifs, nommés p, et des atomes négatifs, nommés n. On notera que, dû à la récursivité de notre définition, on peut avoir des opérateurs d'union sous les opérateurs d'intersection (si on développe les types flèches et tuples). On appellera quand même cette forme une DNF par la suite, par mesure de simplicité. Les atomes de bases ne sont représentés que comme des unions car il sont très simplement simplifiables.

On peut simplifier cette définition en transformant la partie sur les tuples en une union d'union :
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
  t ::= or.big_i b_i or or.big_i ( and.big_j p_1^(i j) -> p_2^(i j) and and.big_j not(n_1^(i j) -> n_2^(i j))) or or.big_i (t_1^i times t_2^i)
$


= Génération d'un témoin

== Définition d'un témoin

Un témoin est un habitant de notre type, c'est à dire une valeur constante appartenant à $[|t|]$. Notre but est, pour chaque cas de base, de trouver un habitant de ce cas, et pour chaque constructeur, de chercher récursivement un témoin pour chacune de ses parties.

==== Exemple
16 est un témoin de $Int or Bool$.

Pour trouver un habitant d'une fonction $f$ de type $t_1 -> t_2$, il faut un langage qui puisse prendre un habitant de $t_1$ et renvoyer le résultat de $f("Witness"(t_1)) = "Witness"(t_2)$.  On pourrait utiliser des $lambda$ termes mais cela serait complexes pour les types récursifs. Enfin, savoir que $42 -> 43$ est un habitant de $Any -> Int$ ne nous aide pas vraiment. Le procédé est donc complexe est contre-productif, nous avons donc choisis de considérer les types flèches (de la forme $or.big_i ( and.big_j p_1^(i j) -> p_2^(i j) and and.big_j not(n_1^(i j) -> n_2^(i j)))$) comme des cas de base. On notera
$ A ::= and.big_i (p_1^i -> p_2^i) and and.big_j not(n_1^j -> n_2^j) $
Cela va permettre de réécrire une nouvelle fois notre définition de type :
$ t ::= or.big_i b_i or or.big_i A_i or or.big_i (t_1^i times t_2^i) $

Un témoin est donc soit une constante d'un cas de base, soit un type flèche, soit un tuple.
On propose donc comme type témoin :
$ w ::= c | A | (w,w) $


==== Exemple :
$w = (42, (True, False))$ est un témoin correct dans notre syntaxe.

== Définition de $w >> t$

On peut donc créer l'algorithme type_of(w) qui pour tout témoin w renvoie le type t contenant uniquement w :

#rule_to_ty

On peut étendre cet algorithme afin que pour tout témoin w, il renvoie le type t tel que $w lt.eq.slant t$. On l'appellera $w >> t$ et aura les règles suivantes : 

#rule_w

==== Exemple
On veut montrer que $w = (3, (True, Int -> Int))$ est bien un témoin de $t = (Int, (Bool, BigZero -> BigOne))$ :

#align(center, exemple_w2)

= Algorithme

== Présentation de l'algorithme

On peut maintenant décrire le fonctionnement de l'algorithme qui pour chaque type t associe un témoin w (qu'on notera $t ~> w$ et appellera Witness(t)) qui a les règles suivantes :

#rule_t

Ici, $Delta$ est l'ensemble des types déjà visité par l'algorithme. Ainsi, si l'on retombe sur le même type, on sait que celui-ci est infini, donc vide (comme expliqué ici *RAJOUTER LIEN*). On interdit donc de repasser plusieurs par un type déjà visité avec la règle $t in.not Delta$.

==== Exemple :
On a $t = (Int, (Int -> Bool) or (Bool -> Int))$

Cela nous donne l'arbre :

#align(center, exemple_t1)

On peut ainsi vérifier que $w = (42, Int -> BigZero)$ est bien un témoin de $t = (Int, (Int -> Bool) or (Bool -> Int))$ :

#align(center, exemple_w1)

== Preuve de terminaison de l'algorithme

#theorem(variant: "Théorème")[
  Pour tout type $t$ non-vide, $t ~> w$ termine.
]

#proof(title: "Preuve ")[

  On a, par définition, que $Delta subset.eq $*$beth$*, donc $Delta$ est de taille finie. On pose $u$ le nombre d'unions directes dans notre terme, avec $u =1$ si l'on choisit le membre de gauche, et $u = u-1$ si l'on choisit le membre de droite, et $s ::= 1 "si" |-""_s, 0 "si" |-""_m.$\
  Alors on peut construire le nombre $(|$*$beth$*$ \\ Delta|,u,s)$ Montrons que, quelque que soit la règle suivie, ce nombre décroît sur l'ordre lexicographique, assurant donc la terminaison de l'algorithme :

  Pour $"Base"_t$ : il suffit de prendre un atome de $or.big_i b_i$, ce qui se fait en temps fini.

  Pour $->_t$ : il suffit de prendre un atome de $A$, ce qui se fait aussi en temps fini.

  Pour $times_t$ : $s$ passe de 1 à 0 car on passe d'une règle $|-""_s$ à des règles $|-""_m$, on a donc bien  $(|$*$beth$*$ \\ Delta|,u,0) lt_("lex") (|$*$beth$*$ \\ Delta|,u,1)$.

  Pour $or_1_t$ : $u$ passe à 1, donc on a bien $(|$*$beth$*$ \\ Delta|,1,1) lt_("lex") (|$*$beth$*$ \\ Delta| ,u,1)$

  Pour $or_2_t$ : $u$ passe à $u - 1$, donc on a bien $(|$*$beth$*$ \\ Delta|,u - 1,1) lt_("lex") (|$*$beth$*$ \\ Delta|,u,1)$

  Pour $t in.not Delta$ : $u$ est susceptible d'augmenter, mais $Delta$ augmente, donc $|$*$beth$*$ \\ Delta|$ décroît de 1,on a donc bien $(|$*$beth$*$ \\ Delta| -1,u',1) lt_("lex") (|$*$beth$*$ \\ Delta|,u,0)$

Donc par induction fondée sur l'ordre lexicographique de $(|$*$beth$*$ \\ Delta|,u,s)$, pour tout type $t lt.eq.not BigZero, t~> w$ termine. 
]

== Preuve de sûreté

#theorem(variant: "Théorème")[
  Pour tout type $t$ non-vide, $"si" emptyset |-""_s t ~> w "alors" w >> t$.
  En d'autres termes, $forall t, "type_of"("Witness"(t)) lt.eq.slant t$.
]

#proof(title: "Preuve ")[
  On veut prouver $P(t) ::= "Si" emptyset |-""_s t ~> w "alors" w >> t$ :\
  On prouve par induction sur les règles d'inférences de $t ~> w$ :

  Pour $"Base"_t$ : Supposons $|-""_s b ~> w$, alors par $"Base"_t$, $w = c lt.eq.slant b$, donc $w = c in [|b|]$, donc $w >> b$.

  Pour $->_t$ : Supposons $|-""_s A ~> w$, alors par $->_t$, $w = w_1 -> w_2 lt.eq.slant A$ , donc par $->_w$, $w >> A$.

  Supposons maintenant $P(t_1)$ et $P(t_2)$.

  Pour $times_t$ : Supposons $(t_1 times t_2) ~> (w_1 , w_2)$, alors par $times_t$, $t_1 ~> w_1$ et $t_2 ~> w_2$, donc par $P(t_1)$ et $P(t_2)$, on a $w_1 >> t_1$ et $w_2 >> t_2$, donc par $times_w$, $(w_1 , w_2) >>(t_1 times t_2)$.

  Pour $or_1_t$ : Supposons $t_1 or t_2 ~> w$, alors par $or_1_t$, $t_1 ~> w$, donc par $P(t_1)$ on a $w >> t_1$, or $t_1 lt.eq.slant t_1 or t_2$ donc par $"Sous-type"_w$, $w >>  t_1 or t_2$.

  Pour $or_2_t$ : Supposons $t_1 or t_2 ~> w$, alors par $or_2_t$, $t_2 ~> w$, donc par $P(t_2)$ on a $w >> t_2$, or $t_1 lt.eq.slant t_1 or t_2$ donc par $"Sous-type"_w$, $w >>  t_1 or t_2$.

  Donc pour tout type $t$ non-vide, $"si" emptyset |-""_m t ~> w "alors" w >> t$.
]

= Extensions

Des extensions ont été rajoutés aux types ensemblistes déjà présents pour couvrir certaines types précis : les n-uplets, les tags et les records. Tout ceux-ci ne sont que des versions spécifiques des tuples, ils ne seront donc pas traités sur le plan théorique. De plus, nos cas de bases peuvent être de 2 types : Int et Enum. On peut donc étendre notre définition de témoin :
$ w ::= i in [|Int|] | e in [|Enum|]| A | (w, w , ... , w) | "tag"(w) | {l_i : w ... l_n : w} $

== Tags
Les atomes de tags sont des tuples avec un type Tag (équivalent à un type string) en premier membre et un type $t$ en deuxième. Ils servent à marquer certains types pour ne pas être confondus (ex : $"foo"(Int)$).

== Records
Les atomes de records sont de la forme $ r ::= {"bindings" : ("Label" times f) "map"; "tail" : f; "exists" : ("Label Set" times f ) "Map"} $
- Ici, le type $f$ est une extension de notre type $t$ qui inclus les types optionnels (ex : $f = Int?$). On le définit comme $f in BigOne union bot$, $bot$ dénotant le type absent.
- Le bindings est un champ où l'on place toutes les variables nommées de notre record.
==== Exemple
${x : Int; y : Int?; "prédicat" : Bool}$

- La tail $f'$ indique si notre record est ouvert ou fermé (donc s'il peut avoir des variables supplémentaires non nommées).
==== Exemple
${x : Int;" " y : Int;;" " Int?}$ pour un système de coordonnées à au moins 2 dimensions.

- Pour chaque paire $(L_i : e_i)$ de exists, $L_i$ indique les noms que la variables ne peut PAS prendre et $e_i and f'$ indique son type.
==== Exemple
${x : Int; y : Int;; Any?;; {w;z} : Bool?}$ pour indiquer que les variables $w$ et $z$ ne peuvent pas avoir le type $Bool$ si elles existent.

= Implémentation

L'algorithme va essayer de trouver un témoin dans chacune des 6 grandes catégories (Int, Enum, Arrows, Tag, Tuple, Record) dans cet ordre, et s'arrêter dès qu'un est trouvé. Si aucun témoin n'est trouvé, on considère le type comme vide et on lève une exception.
== Cas de bases

=== Int
Les entiers sont représentés comme des intervalles. Il existe 3 cas possibles :
- $t = ]-oo ; +oo[$ : l'algorithme retourne 42.
- $t = ]-oo; i ]$ ou $t = [ i ; +oo[$ :  retourne $i$.
- $t = [i_1; i_2]$ : retourne $i_1$.

=== Enum
Enum contient tout les types énumérés, incluant notamment les booléens (et les Strings ?). Il peuvent être définis de 2 manières :
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
==== Exemple
${x : Int; y : Int?; "prédicat" : Bool}$ donnera ${x : 42; "prédicat" : True}$.

- Si la tail $f'$ est requise, on l'ajoute dans la tail de $w$.
==== Exemples
+ ${x : Int;;" " Bool}$ donnera ${x: 42;; Bool}$.\
+ ${x : Int;;" " Int?}$ donnera ${x :42}$.
- Pour chaque paire $(L_i : e_i)$ de exists, si $e_i and f$ est requis, alors on crée un label $l'_i in.not L_i$, on cherche récursivement un témoin $w'_i$ de $e_i and f$ et on ajoute $(l'_i : w'_i)$ *au bindings*.
==== Exemple
${x : Int; y : Int "";;"" Any? "" ;; "" {w;z} : Bool}$ donnera ${x : 42 "" ; "" y : 42 "" ; "" a : True}$

= Un bug !
Si on crée $alpha$ une variable de type, alors TY.get_descr($alpha$) = $BigOne$, donc Witness($alpha$) = $42$. Mais d'après le sous-typage, $42 lt.eq.not alpha$. :(


#bibliography("bibliography.bib", full: true)