mardi 11 février 2020, 14:19:46 (UTC+0100)
==========================================

Premier objectif: un programme qui construit un graphe à partir d'un ensemble de déclarations de fonctions, explore ce graphe en largeur et affiche les N premiers chemins trouvés.


vendredi 28 février 2020, 19:01:30 (UTC+0100)
=============================================

Les chemins sont pollués par les morphismes "<" et ">". Pour réduire le nombre de chemins, ajout d'un noeud terminal "Done". On garde seulement ceux qui terminent par Done.


lundi 2 mars 2020, 09:49:46 (UTC+0100)
======================================

Objectif pour la semaine: générer le graphe des scripts OpenMOLE.

- Résoudre le problème des chemins pollués par des suites infinies de "<" et ">",
- Écrire la liste des constructeurs de scripts OpenMOLE.
- Générer le graphe au format DOT (graphviz)
- Afficher le graphe.
 
Optionnel: 
- Écrire le parseur de liste de constructeurs.
- Générer un script openmole étant donné un chemin en entrée.


vendredi 6 mars 2020, 11:55:39 (UTC+0100)
=========================================

Pour résoudre le problème de pollution par les suites infinies morphismes "<" et ">", j'ai créé des shortcuts, c-a-d des morphismes "&f . < . < ... <" qui correspondent à des chemins utiles. 

Une mesure supplémentaire pour simplifier le graphe: définir un nœud de départ START dont part des morphismes qui pointent vers des nœuds permettant de construire des scripts openmole (OMS). 


jeudi 2 avril 2020, 17:53:08 (UTC+0200)
=======================================

Pour restreindre le nombre de chemins possibles dans le graphe, de telle sorte qu'il n'y ait plus qu'un seul chemin pour construire chaque script, chaque
constructeur défini par l'utilisateur donne lieu à un seul morphisme construit
par la fonction 'cons::using': un constructeur x de type a1 -> a2 ... -> an -> b donne un morphisme de type (b -> c) -> (a1 -> ... -> an -> c). Valable aussi
pour n = 0.

Le nœud de départ est maintenant le type SCRIPT -> SCRIPT, et le nœud final SCRIPT. Étant donné la manière dont on crée les morphismes à partir des constructeurs, un morphisme entre le nœud de départ et celui d'arrivée est de type (SCRIPT -> SCRIPT) -> SCRIPT. Ainsi, pour obtenir une valeur à partir d'un d'eux, il faut lui appliquer la fonction identité.

Implémentation de la fonctionnalité Interact.
