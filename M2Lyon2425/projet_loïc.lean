/-
Bonjour
Mon idée de projet se porte sur le théorème de Cauchy sur les groupe (pour tout diviseur premier du cardinal d'un
goupe fini , il existe un élément de cet ordre)

La preuve que je voudrais formaliser est celle avec les actions de groupe :
on fait agir le groupe le groupe cyclique sur un certain ensemble et on peux en déduire par
l'équation aux classes l'existence d'un tel élément

Je n'ai pas encore trouvé de livres reprenant éxactement la preuve que j'avais en tête
mais l'idée de la preuve se trouve sur wikipédia .

Le théorème se trouve déjà sur mathlib sous le nom " _root_.exists_prime_orderOf_dvd_card" avec une preuve
qui est je pense celle que je veux formaliser mais j'avoue de pas vraiment tout comprendre de ce qui est écrit

Je pense qu'une des diffucultés de la preuve est le fait que certains argument (de dénombrement notamment)
sont rarement très rigoureux dans cette preuve et les formaliser pourrait être difficile.


Si jamais tout se passerait mieux que prévu et que la preuve se révélerait "trop facile" , je pourrais aussi
formaliser une autre preuve de se résultat par récurrence sur le cardinal du groupe


Voici le squelette de la preuve que je proposer de formaliser , la preuve se trouve dans le livre "Théorie des groupes"
de Félix Ulmer.


Soit G un groupe fini et p un nombre premier divisant le cardinal de G
On considère H le sous groupe engendré par le p-cycle (1,2,3,...,p) dans Sₚ .
On considère X le sous ensemble des p-uplet (g₁,g₂,...,gₚ) de G tel que g₁g₂...gₚ = e
On a alors une action de H sur X par permutations cyclique des composantes : (1,2,3,...,p) ⬝ (g₁,g₂,...,gₚ) = (gₚ,g₁,g₂,...,g_p-1)
L'élément gₚ étant déterminé par les p-1 autres éléments , on a que X est de cardinal |G|^(p-1)
On utilise ici un resultat général sur les p-groupe : |Xᴴ| ≅ |X| [mod p] où Xᴴ désigne les point fixes de X sous l'action de H
Ce résultat se démontre grâce à l'équation aux classes.
On a alors p ∣  |Xᴴ| car p ∣ |X|
Or , (e,e,...,e) ∈ Xᴴ donc cet ensemble est non vide et donc de cardinal au moins p .
Les éléments de Xᴴ étant de la forme (g,g,...,g), on a bien l'éxistence d'un élément d'ordre p dans G














-/
