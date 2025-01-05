# Introduction

On s'intéresse ici, pour `α` un type quelconque, aux relations binaires sur `α`, c'est à dire aux fonctions `α → α → Prop`. Pour `f : α → α → Prop` fixé, on  peut voir cette relation binaire comme un flèche, si `x y : α`, on peut aller de `x` à `y` si et seulement si `f x y`. On peut alors s'intéresser à de la réécriture : est-il possible d'aller de `x` à `y` *via* un chemin ?

Dans un premier temps on remarque que le type `α → α → Prop`, abbrégé en `ARS α`, est naturellement muni d'une structure d'algèbre de Kleene (un anneau non-commutatif, dont l'addition est idempotente, et muni d'une opération spéciale `∗` (en notation postfixe) vérifiant différentes propriétés).

Ceci étant fait, il est beaucoup plus simple de vérifier certaines propriétés d'opérations sur `ARS α` (de même qu'il est plus facile de les énoncer).

# But

Nous verrons les preuves des théorèmes 2.3.8 et 2.3.9 ainsi que l'implémentation de quelques définitions (formes normales, terminaison, normalisation (faible et forte), …) du pdf de P. Malbos trouvables là : (cra24_chapitre2.pdf).

J'ai, en essayant de faire la preuve du théorème 2.3.9, beaucoup dérivé et ai fini par montrer le principe d'induction noetherienne (définition en 2.3.15, théorème en 2.3.16).

Je souhaitait initialement prouver le théorème 2.3.9. Je ne l'ai pas fait par manque de temps.

# Organisation du dossier

La structure du dossier et de ces preuves est la suivante :
1. on prouve d'abord des résultats portants sur les algèbres de Kleene (M2Lyon2425/projet/KleeneAlgebra.lean) ;
2. on montre que l'on peut munir `ARS α` d'une structure d'algèbre de Kleene (M2Lyon2425/projet/ARSinstKleene.lean) ;
3. on prouve des résultats sur les ARS :
  1. d'abord, sans les lemmes spécifiques aux algèbres de Kleene (M2Lyon2425/projet/lemmesARS.lean),
  2. puis avec (M2Lyon2425/projet/lemmesARSKleene.lean) ; 
4. enfin, on définit quelques propriétés et on montre le théorème 2.3.8 voulu (M2Lyon2425/projet/projet.lean) ;
5. finalement, on montre que le principe d'induction noetherienne est valide sous les bonne conditions (M2Lyon2425/projet/noetherianInduction.lean).

Les deux autres fichier contiennent des résultats inutilisés (car inutiles ou inaboutis).