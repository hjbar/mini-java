---
title: Rapport pour le _projet de Compilation_
author: Hugo BARREIRO & Paul-Alexis RODRIGUEZ
---

\newpage
\tableofcontents
\newpage

# Compiler le projet

Pour compiler le projet, il suffit d'utiliser la commande _make_ à la racine. Pour lancer les tests, on peut utiliser les commandes _make test_, _make test-typing_ et _make test-compile_, également à la racine. Pour générer le _.pdf_ du rapport, il faut utiliser _make_ à l'intérieur du répertoire _doc_.

# Organisation du code

Dans le répertoire _src_, on trouve deux répertoires : _typing_ et _compile_.

Dans _typing_, on retrouve 4 fichiers différents :

- _typing.ml_, contient les fonctions principales permettant de typer le programme.
- _typing_print.ml_, contient des fonctions d'affichage pour du débogage.
- _typing_utils.ml_, contient des définitions, des fonctions d'une ligne et des fonctions simples permettant d'améliorer la lisibilité du code.
- _typing_algo.ml_, contient des fonctions plus compliquées que celles de _typing_utils.ml_, permettant d'alléger le fichier principal _typing.ml_.

Dans _compile_, on retrouve 3 fichiers différents :

- _compile.ml_, contient les fonctions principales permettant de compiler le programme.
- _compile_utils.ml_, contient des définitions et des fonctions ne contenant pas d'assembleur, permettant d'alléger le fichier principal.
- _compile_algo.ml_, contient des fonctions contenant de l'assembleur, permettant d'alléger le fichier principal.

# Choix techniques

## Schéma de compilation

Nous avons décidé de toujours laisser la valeur de la dernière expression compilée au sommet de la pile. Ceci permet de la récupérer aisément grâce à l'instruction _popq_. De plus, l'avantage de ne pas stocker les valeurs des expressions dans les registres est d'être sûr de ne jamais écraser une valeur qui ne devait pas l'être.

Pour les registres temporaires (pour compiler les expressions, par exemple), nous avons décidé d'utiliser les registres _r12_, _r13_, _r14_ et _r15_. En effet, ces registres sont callee-saved. Ainsi, un appel de fonction (comme _printf_, par exemple) ne peut pas écraser les valeurs stockées dans ces registres (au pire, la fonction doit restaurer ces valeurs).

Pour ce qui est des appels de fonctions (_call_ et _new_), nous suivons le schéma proposé dans le sujet. Il en est de même pour les objets, c'est-à-dire que nous utilisons la structure proposée pour les _descripteurs de classe_ et les _attributs_.

## Choix

### Typage

Nous prenons soin de préciser la localisation des erreurs de la meilleure manière possible. Ainsi, nous essayons d'utiliser les localisations les plus internes. Par exemple, lorsque _true_ && _2_ soulève une erreur, on indique la position de _2_ et non de &&. Même si cela a pour effet négatif d'avoir un code plus verbeux par moment, cela vaut le coup à notre avis.

De plus, nous avons décidé de simplifier le _up-cast_ au typage. C'est-à-dire qu'on ne place pas le _cast_ dans l'_AST_, mais que l'on place l'expression qui devait être _castée_ seulement. S'il est vrai que l'on "perd" du temps au typage, cela va toute fois permettre de gagner un peu de temps à l'exécution, ce qui est souvent souhaitable. On remarque finalement que si l'on voulait gagner du temps au typage, on pourrait simplement supprimer cette simplification, puisque le code à l'exécution est le même pour le _down-cast_ et le _up-cast_.

### Compilation

Nous avons décidé de ne jamais laisser le programme _crasher_, par exemple avec une _segmentation fault_. Pour ce faire, on exécute un _exit 1_ lorsque nécessaire. De cette manière nous vérifions dynamiquement si l'on effectue une division (ou un modulo) par 0 ou si l'on tente d'accéder à un objet _null_ lorsque ce n'est pas autorisé.

## Implémentation

### Typage

Tout d'abord, on utilise deux références globales : une pour la _classe_ courante et une pour le type du _return_ courant. Une autre solution aurait été de les stocker dans l'environnement, mais ici ce n'est pas nécessaire, car on ne peut pas définir une classe dans une classe ni une méthode dans une méthode. Ainsi, la valeur de ces deux références est toujours cohérente.

Ensuite, on utilise également une _hashtbl_ globale pour stocker les différentes _classes_ afin de pouvoir y accéder efficacement.

Enfin, nous avons défini de nouveaux opérateurs pour simplifier la lisibilité du typage :

- =*, l'égalité sur les types, renvoie _true_ si et seulement si les classes sont les mêmes ou si les types atomiques sont les mêmes ; renvoie _false_ sinon.
- <>\*, défini simplement comme la négation de =*.
- <=*, renvoie _true_ si le membre gauche est le sous-type du membre droit ; renvoie _false_ sinon.
- <=>*, renvoie _true_ si l'un des deux membres est sous-type de l'autre ; renvoie _false_ sinon.

### Compilation

Nous avons choisi de compiler en deux temps : d'abord la partie _text_, puis la partie _data_.

Pour la partie _text_, on compile toutes les _classes_, puis les fonctions utilitaires, telles que _print_string_, par exemple.

Pour la partie _data_, nous avons créé une _(string * string) Queue.t_. De cette façon, à chaque fois que l'on rencontre une string constante, on crée un nouveau _label_ que l'on associe avec la string dans la _queue_. Une fois tout le code compilé, nous avons toutes les strings constantes, que l'on peut donc compiler dans la partie _data_. Nous avons utilisé la même idée pour les descripteurs de classe en utilisant une _(string, data) Hashtbl.t_. Chaque fois que l'on rencontre une nouvelle classe, on crée son descripteur que l'on stocke dans la _hashtbl_. Après avoir compilé toutes les classes, on dispose donc de tous les descripteurs. On peut alors également les compiler dans la partie _data_.

Pour les constructions utilisant des _labels_, comme _if_, nous avons décidé de les compiler en utilisant une fonction extérieure à la fonction principale. On peut définir une fonction stockant dans sa clôture un compteur local à cette fonction (on ne peut pas y accéder en dehors) mais global à une fonction interne auxiliaire. Ainsi, on peut numéroter nos labels indépendamment des autres. D'ailleurs, le compilateur OCaml nous a beaucoup surpris (il est très fort) : on peut passer en argument à une fonction, une fonction qui est actuellement en train d'être définie afin de l'utiliser dans la définition de cette autre fonction...

# Problèmes

Nous avons rencontré des problèmes lors de la compilation de _new_.

En effet, au départ, dans notre schéma de compilation, lors d'un appel à _new_, nous allouions un espace dans le tas, dont on récupérait l'adresse dans le registre _rax_. Nous rajoutions ensuite le _descripteur de classe_ dans l'espace présent à l'adresse donnée par _rax_. Puis, nous faisions un _push_ sur la pile de l'adresse contenue dans _rax_. Ensuite, nous compilions et empilions les arguments et _this_, et enfin, nous appelions le constructeur.

Le problème était que lorsque l'on faisait appel à des constructeurs récursifs, notamment pour les classes récursives (typiquement des listes chaînées, par exemple), le contenu du registre _rax_ était écrasé par les nouveaux appels à _malloc_. Cela avait pour conséquence de ne garder que la toute dernière instance créée, et non la première, dans la variable.

Pour remédier à ce problème, nous avons décidé de _push_ le contenu de _rax_ afin de conserver l'adresse renvoyée par _malloc_ au sommet de la pile, juste avant d'empiler les arguments et _this_ pour l'appel au constructeur. De cette manière, lorsque l'on dépile les arguments et _this_, nous sommes sûrs de pouvoir récupérer la bonne instance de l'objet au sommet de la pile.

Cependant, nous avons constaté que cette version était elle-même problématique pour des raisons non visibles dans le jeu de tests donné. En effet, dans la version précédente, il y avait deux _push_ de _rax_ sur la pile : un avant la compilation des arguments et un après (le premier pour sauvegarder l'adresse et le deuxième pour permettre au constructeur d'accéder à l'objet avec _this_). Or, pendant la compilation des arguments, rien n'empêche qu'un argument soit une expression contenant un appel à une fonction externe (telle que _printf_), écrasant elle-même le registre _rax_. Ceci est problématique pour le deuxième _push_ de _rax_ (ce dernier contient maintenant la valeur qui a écrasé l'objet).

Pour remédier à cela, nous avons finalement décidé de récupérer l'objet dans la pile à l'adresse où nous l'avions empilé auparavant, avant de faire le deuxième _push_ (ceci nous garantit d'empiler et de récupérer le bon objet). Le test _tests/exec/perso1.java_ permet de vérifier que ce problème ne soit plus présent.