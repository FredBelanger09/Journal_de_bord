#import "@preview/arkheion:0.1.2": arkheion, arkheion-appendices
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/tdtr:0.5.5": tidy-tree-graph
#import "@preview/thmbox:0.3.0": *


#import "macros.typ": *
#import "rules.typ": *


#show: shorthands.with(($|-$, $tack.r$), ($~=$, $tilde.eq$))
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
#show: thmbox-init()

#outline(depth: 3)

= Introduction
Le but du stage a été de créer une fonction permettant, pour tout type non-vide, de trouver un habitant de ce type, appelé témoin. Ce témoin permet d'afficher un exemple lors de la diffusion d'un message d'erreur pour mauvais typage.

==== Exemple
On a une fonction $f : Int -> Int$ et une variable $x : Int or Bool$. Alors l'application $f(x)$ est mal typée, car $Int or Bool "n'est pas un sous-type de" Int$. On cherche donc un témoin de $(Int or Bool) \\ Int = Bool$, ce qui peut rendre $True$ ou $False$. Pour des types plus complexes, on veut automatiser le processus, ce qui amène à l'algorithme "Witness" expliqué ici.


= Présentation des types ensemblistes

== DONNER UN NOM ICI
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

On peut aussi représenter celà sous la forme d'un graphe cyclique en remplaçant la feuille $t$ par une flèche vers $\_or\_$. Ceci nous permet d'avoir une définition de type qui n'a pas besoin de définitions explicites pour la récursion.

Enfin, on considère les types infinis comme vides, car ils sont inconstructibles en pratique (ex : $t = (Int, t) lt.eq.slant BigZero$ ).

Dans un premier temps, nous allons ignorer les variables de types pour la génération du témoin.

== PARLER DES PLINTHS (cf https://usr.lmf.cnrs.fr/~kn/files/popl2015.pdf page 39) $ Im$

== Existence d'une forme normal A ECRIRE
#lemma(variant: "Lemme")[
  $forall t , t lt.eq.slant BigOne times BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$
]<lemma-one>

#proof[
  Si $t lt.eq.slant BigOne times BigOne$ alors :

  $t &= or.big (and.big_i (p_1^i, p_2^i)and and.big_j not(n_1^j, n_2^j))\
  &= or.big ((and.big_i (p_1^i, p_2^i))\\ or.big_j (n_1^j, n_2^j))\
  &= or.big ((and_i p_1^i,and_i p_2^i)\\ or.big_j (n_1^j, n_2^j))$ par commutativité de $and$

  Montrons par récurrence sur $or.big_j (n_1^j, n_2^j)$ que t est bien une union :

  On a bien $(and_i p_1^i,and_i p_2^i)$ qui est une union d'un seul élement.

  On a maintenant $or.big_i (t_1^i,t_2^i)$ une union, montrons que $or.big_i (t_1^i,t_2^i) \\ (n_1,n_2)$ est une union :
  $or.big_i (t_1^i,t_2^i) \\ (n_1,n_2) & = or.big_i ((t_1^i,t_2^i) \\ (n_1,n_2)) \
   &= or.big_i ((t_1^i \\ n_1,t_2^i) or (t_1^i,t_2^i \\ n_2))$ qui est une union.

  Donc par récurrence, $forall t , t lt.eq.slant BigOne times BigOne => exists (t_1^i, t_2^i), t tilde.eq or.big_i (t_1^i, t_2^i)$.
]

= Génération d'un témoin

== Définition d'un témoin

Un témoin est un habitant de notre type, c'est à dire une valeur constante apartenant à $[|t|]$. Notre but est, pour chaque cas de base, de trouver un habitant de ce cas, et pour chaque constructeur, de chercher récurisvement un témoin pour hcacune de ses parties.

Contrairement à ce que voudrait la logique, les atomes de la forme $and.big (t_1 -> t_2) and and.big not(t_1 -> t_2)$ sont ici considérés comme des cas de base, car toutes les fonctions sont habitées, et connaitre uniquement un cas d'utilisation serait complexe et improductif. on considère donc que $A ::= and.big (t_1 -> t_2) and and.big not(t_1 -> t_2)$ est un cas de base.
CHANGER TOUT CA CF PARTIE BAS DROITE DU TABLEAU

On propose donc comme type témoin :
$ w ::= c | A | w times w $

En pratique, on a $c ::= i in [|Int|] | e in [|Enum|]$

==== Exemple :
$w = (42, (True, False))$ est un témoin correct dans notre syntaxe

== Définiton de $w :t$ RETRANSFORMER EN L'ALGO "type d'un témoin"

On peut donc définir un prédicat $w : t$ qui est vrai si et seulement si w est un témoin de t, avec les règles suivantes :

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

== TERMINAISON A METTRE ICI, PARLER DE L'ORDRE LEXICO $(|Im \\ Delta |, u , s)$ avec u = 1 si union de gauche, u-1 si union de droite; s = 1 si $|- m$, 0 si $|- s$

#theorem(variant: "Théorème")[
  Pour tout type $t$ non-vide, $t ~> w$ termine.
]

#proof(title: "Preuve ")[
  On peut déjà noter que pour tout type t, $Delta$ a une taille maximale finie, car il est au maximum de la taille l'ensemble de tout les sous-types de t (qui est fini car t est régulier selon la @regulier).

  A chaque appel récursif, $Delta$ grandit, nous ne pouvons donc pas avoir d'appel récursif infinis. On peut donc ignorer ce cas là par la suite.

  En peut aussi dire qu'en pratique, nos types sont stockés sous la forme de DNF, on a donc :

  $ t = or.big (and.big b) or.big (and.big t_1 -> t_2) or.big (and.big (t_1 times t_2)) $

  Grâce au @lemma-one, on peut réécrire t comme :
  $ t = or.big (and.big b) or.big (and.big t_1 -> t_2) or.big (t_1 times t_2) $


  Il suffit donc de montrer que $t ~> w$ termine si $t = and.big b$, $t = and.big t_1 -> t_2$, $t=t_1 times t_2$ et $t = t_1 or t_2$

  Si $t = and.big b$, alors il suffit de prendre un atome de $and.big b$, ce qui se fait en temps fini.

  Si $t= and.big t_1 -> t_2$, alors $and.big t_1 -> t_2$ est une solution, donc cela se fait aussi en temps fini.

  Supposons maintenant que $t_1 ~> w_1$ et $t_2 ~> w_2$ terminent.

  Si $t = t_1 times t_2$, alors par $times_t$, $t_1 times t_2 ~> (w_1 , w_2)$ termine si $t_1 ~> w_1$ et $t_2 ~> w_2$ terminent, ce qui est le cas par hypothèse. Donc $t_1 times t_2 ~> (w_1 , w_2)$ termine.

  Si $t = t_1 or t_2$, alors :
  - Par $or_1_t$, $t_1 or t_2 ~> w$ termine si $t_1 ~> w$ termine, ce qui est le cas par hypothèse
  - Par $or_2_t$, $t_1 or t_2 ~> w$ termine si $t_2 ~> w$ termine, ce qui est le cas par hypothèse.
  Donc si $t = t_1 or t_2$, alors $t ~> w$ termine.

  Donc par induction, pour tout type t non-vide, $t ~> w$ termine.
]

== SURETE A METTRE ICI

#theorem(variant: "Théorème")[
  Pour tout type $t$ non-vide, $"si" emptyset |-""_s t ~> w "alors" w:t$.
]

#proof(title: "Preuve ")[
  On définit $P(t, w) ::= "Si" emptyset |-""_s t ~> w "alors" w:t$\
  On prouve par induction sur les règles d'inférences de $t ~> w$ :

  Si $|-""_s b ~> w$, alors par $"Base"_t$, $w = c lt.eq.slant b$, donc $w = c in [|b|]$, donc $w:b$.

  Si $|-""_s (and.big t_1 -> t_2) ~> w$, alors par $->_t$, $w = w_1 -> w_2 lt.eq.slant and.big t_1 -> t_2$ , donc par $->_w$, $w : and.big t_1 -> t_2$

  Supposons maintenant $P(t_1,w)$ et $P(t_2,w)$.

  Montrons que $P(t_1 times t_2, (w_1 , w_2))$ :\ Si $(t_1 times t_2) ~> (w_1 , w_2)$, alors par $times_t$, $t_1 ~> w_1$ et $t_2 ~> w_2$, donc par hypothèse, $w_1 :t_1$ et $w_2 :t_2$, donc par $times_w$, $(w_1 , w_2) : (t_1 times t_2)$.

  Montrons que $P(t_1 or t_2, w)$ :\ Si $t_1 or t_2 ~> w$, alors par $or_1_t$, $t_1 ~> w$, donc $w:t_1$, or $t_1 lt.eq.slant t_1 or t_2$ donc par $"Sous-type"_w$, on a $w : t_1 or t_2$, donc si .

  Donc pour tout type $t$ non-vide, $"si" emptyset |-""_m t ~> w "alors" w:t$.
]

= EXTENSIONS

, ainsi que des extensions pour les tags, les n-uplets et les records, ce qui donne :
$ w ::= i in [|Int|] | e in [|Enum|]| A | w times w times ... times w | "tag"(w) | {l_i : w ... l_n : w} $
Les tags, les n-uplets et les records ne sont en réalité que des cas particuliers des tuples, ils ne seront donc pas traités sur le plan théorique.

EXPLIQUER LES n-UPLETS, LES TAGS ET LES RECORDS ICI

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
Comme dit plus haut, on considère les atomes de la forme $and.big (t_1 -> t_2) and and.big not(t_1 -> t_2)$ comme des cas de base.
On va donc prendre tout les atomes positifs de t, et y rajouter un par un les atomes négatifs de t. Si au moment d'un ajout, l'intersection des atomes positifs et négatifs donne un sous-type de t, c'est notre témoin.


== Constructeurs

=== Tuple

Les n-uplets peuvent, comme les Enum, être défini comme les éléments présents dans $t$ ou comme les éléments présents dans $not t$.
- Si on a la liste des éléments présents dans $t$, on choisit l'élément e de plus petite arité dont aucun élément n'est vide, et on renvoie un n-uplet de la même taille  et dont chaque élément est le témoin du type à la même position dans e.
- Si on a la liste des éléments présents dans $not t$, on trouve le plus petit entier n tel qu'il n'y ai aucun n-uplet de cette arité dans la liste, et on en renvoie un témoin (usuellement le n-uplet (0,1,...,n))

==== Exemples
+ $(Int, Bool)$ donnera $(42, True)$
+ $Tuple \\ ((Int,) or (Int, Bool))$ donnera $(0,1,2)$

=== Tag

Les tags sont des tuples avec un type Tag (équivalent à un type string) en premier membre et un type $t$ en deuxième. Ils servent à marquer certains types pour ne pas être confondus (ex : $"foo"(Int)$).
Ils sont traités de la même manière que les tuples de taille 2, à l'exception que l'on n'opère pas de récursion sur le premier membre.

==== Exemples
+ $"foo"(Int)$ donnera $"foo"(42)$.
+ $Tag \\ "foo"(Int)$ donnera $"a"(16)$.

=== Records
Les atomes de records sont de la forme $ r ::= {"bindings" : ("Label" times f) "map"; "tail" : f; "exists" : ("Label Set" times f ) "Map"} $
- Ici, le type $f$ est une extension de notre type $t$ qui inclus les types optionnels (ex : $f = Int?$). On le défini comme $f in BigOne union bot$, $bot$ dénotant le type absent.
- Le bindings est un champ où l'on place toutes les variables nommées de notre record.
==== Exemple
${x : Int; y : Int?; "predicat" : Bool}$

- La tail $f'$ indique si notre record est ouvert ou fermé (donc s'il peut avoir des variables supplémentaires non nommées).
==== Exemple
${x : Int;" " y : Int;;" " Int?}$ pour un système de coordonnées à au moins 2 dimensions.

- Pour chaque paire $(L_i : e_i)$ de exists, $L_i$ indique les noms que la variables ne peut PAS prendre et $e_i and f'$ indique son type.
==== Exemple
${x : Int; y : Int;; Any?;; {w;z} : Bool?}$ pour indiquer que les variables $w$ et $z$ ne peuvent pas avoir le type $Bool$ si elles existent.

Pour générer un témoin, on va trouver un atome non vide de notre record, et opéré comme suit :

- Pour chaque paire $(l_i : f_i)$ de bindings, si $f_i$ est requis, alors on cherche récursivement un témoin $w_i$ de $f_i$ et ajouter $(l_i : w_i)$ au bindings de notre témoin $w$.\
==== Exemple 
${x : Int; y : Int?; "predicat" : Bool}$ donnera ${x : 42; "predicat" : True}$.

- Si la tail $f'$ est requise, on l'ajoute dans la tail de $w$.
==== Exemples
+ ${x : Int;;" " Bool}$ donnera ${x: 42;; Bool}$.\ 
+ ${x : Int;;" " Int?}$ donnera ${x :42}$.
- Pour chaque paire $(L_i : e_i)$ de exists, si $e_i and f$ est requis, alors on crée un label $l'_i in.not L_i$, on cherche récursivement un témoin $w'_i$ de $e_i and f$ et on ajoute $(l'_i : w'_i)$ *au bindings*.
==== Exemple
${x : Int; y : Int "";;"" Any? "" ;; "" {w;z} : Bool}$ donnera ${x : 42 "" ; "" y : 42 "" ; "" a : True}$

= Preuve de sûreté
On veut montrer que le socle théorique de notre algorithme est fondé, nous allons donc montrer la terminaison de notre programme, ainsi que la preuve théorique de sa justesse.



== Preuve de la terminaison de $t ~> w$




== Preuve de la justesse de l'algorithme




#bibliography("bibliography.bib", full : true)