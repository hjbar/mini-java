---
title: Rapport pour le _projet de Compilation_
author: Hugo BARREIRO & Paul-Alexis RODRIGUEZ
---

# Compiler le projet

Pour le compiler le projet, il suffit d'utiliser la commande ```make``` à la racine. Pour lancer les tests, on peut utiliser les commandes ```make test```, ```make test-typing``` et ```make test-compile``` également à la racine. Pour générer le ```.pdf``` du rapport, il faut utiliser ```make``` à l'intérieur du répertoire ```doc```.

# Organisation du code

Dans le répertoire ```src``` on trouve deux répertoires ```typing``` et ```compile```.

Dans ```typing```, on retrouve 4 fichiers différents :
    - ```typing.ml```, contient les fonctions principales permettant de typer le programme.
    - ```typing_print.ml```, contient des fonctions d'affichage pour du déboggage.
    - ```typing_utils.ml```, contient des définitions, des fonctions d'une ligne et des fonctions simples permettant d'améliorer la lisiblité du code.
    - ```typing_algo.ml```, contient des fonctions plus compliqués que celles de ```typing_utils.ml``` permettant d'alléger le fichier principal ```typing.ml```.

Dans ```compile```, on retrouve 3 fichiers différents :
    - ```compile.ml```, contient les fonctions principales permettant de compiler le programme.
    - ```compile_utils.ml```, contient des définitions et des fonctions, ne contenant pas d'assembleur, permettant d'alléger le fichier principal.
    - ```compile_algo.ml```, contient des fonctions, contenant de l'assembleur, permettant d'alléger le fichier principal.

# Choix techniques

## Schéma de compilation

Nous avons décidé de toujours laisser la valeur de la dernière expression compilée au sommet de la pile. Ceci permet de la récupérer aisément grâce à l'instruction ```popq```. De plus, l'avantage de ne pas stocker les valeurs des expressions dans les registres est d'être sûr de ne jamais écraser une valeur qui ne devait pas l'être.

Pour les registres temporaires (pour compiler les expressions par exemple) nous avons décider d'utiliser les registres ```r12```, ```r13```, ```r14``` et ```r15```. En effet, ces registres sont ```callee-saved```. Ainsi, un appel de fonction (comme ```printf``` par exemple) ne peut pas écraser les valeurs stockés dans ces registres (au pire la fonction doit restaurer ces valeurs).

Pour ce qui est des appels de fonctions (```call``` et ```new```) nous suivont le schéma proposé dans le sujet. Il est de même pour les objets, c'est-à-dire qu'on utilise la structure proposée pour les ```descripteurs de classe``` et les ```attributs```.

## Implémentation

### Typage

On utilise deux références globales : une pour la ```classe``` currente, une pour le type du ```return``` courent. Une autre solution aurait été des les stocker dans l'environnement mais ici ce n'est pas nécessaire car on ne peut pas définir une classe dans une classe et une méthode dans une méthode. Ainsi, la valeur de ces deux références sont toujours cohérentes.

De plus, on utilise également une ```hashtbl``` globale pour stocker les différentes ```classes``` afin de pouvoir y accéder efficacement. 

### Compilation

Nous avons choisi de compiler en deux temps : d'abord la partie ```text``` puis la partie ```data```. Pour la partie ```text```, on compile toutes les classes, puis les fonctions utilitaires telles que ```print_string``` par exemple. Pour la partie ```data```, nous avons créer une ```(string * string) Queue.t```. Ainsi, à chaque fois que l'on rencontre une string constante, on créer un nouveau ```label``` qu'on associe avec la string dans la ```queue```. Après, avoir compiler tout le code, nous avons donc toutes les strings contantes que l'on peut donc également compiler dans la partie ```data```. Nous avons utiliser la même idée pour les descripteurs de classe en utilisant une ```(string, data) Hashtbl.t```. Ainsi, à chaque fois que l'on rencontre une nouvelle classe, on créer son descripteur que l'on stocke dans la ```hashtbl```. Après avoir compiler toutes les classes, on dispose donc de tous les descripteurs. On peut alors les compiler dans la partie ```data```.

Pour les constructions utilisant des ```labels``` comme ```if```, nous avons décidé de les compiler en utilisant une fonction extérieure à la fonction principale. Ainsi, on peut définir une fonction stockant dans sa cloture un compteur locale à la fonction (on ne peut pas y accéder en dehors) mas globale à la fonction. Ainsi, on peut numéroter nos labels indépendemment des autres. D'ailleurs, le compilateur OCaml m'a beaucoup surpris (il est très fort) : on peut passer en argument à une fonction, une fonction qui actuellement en train d'être définie afin de l'utiliser dans la définition de cette autre fonction :).

# Problèmes

Nous avons rencontré des problèmes lors de la compilation de ```new()```.
En effet au départ dans notre schéma de compilation, lors d'un appel à new, nous allouions un espace dans le tas, dont on récupérait l'adresse dans le registre rax. Nous rajoutions ensuite le descripteur de classe dans l'espace présent à l'adresse donnée par rax. Puis nous faisions un push sur la pile de l'adresse contenue dans rax. Ensuite nous compilions et empilions les arguments et ```this```, et enfin nous appelions le constructeur.
Le problème étant que lorsque l'on faisait appel à des constructeurs récursifs, notamment pour les classes récursives (typiquement des listes chaînées, par exemple), le contenu du registre rax était écrasé par les nouveaux appels à ```malloc```. Ce qui avait pour conséquence de ne garder que la toute dernière instance créée, et non la première, dans la variable.
Pour remédier à ce problème nous avons décidé de push le contenu de rax afin de conserver l'adresse renvoyée par malloc au sommet de la pile juste avant d'empiler les arguments et ```this``` pour l'appel au constructeur. De cette manière lorsque l'on dépile les arguments et ```this```, nous sommes sûrs de pouvoir récupérer la bonne instance de l'objet au sommet de la pile. Cependant nous avons constaté que cette version était problématique pour des raisons non-visibles dans le jeu de tests donné. En effet, dans la version précédente il y avait deux push de rax sur la pile, un avant la compilation des arguments et un après (le premier pour sauvegarder l'adresse et le deuxième pour permettre au constructeur d'accéder à l'objet avec this). Cependant pendant de la compilation des arguments rien n'empêche que l'expression d'un argument soit un appel à une fonction écrasant elle même le registre rax. Ceci est problématique puisque le deuxième push, va push rax (qui contient maintenant la valeur qui a écrasé l'objet).
Pour remédier à ceci nous avons finalement décider de récuperer l'objet dans la pile à l'adresse où nous l'avions empilé auparavant avant de faire le deuxième push (ceci nous garantit d'empiler et de récuperer le bon objet). Le test ```tests/exec/perso1.java``` permet de vérifier que ceci ne soit plus le cas.
