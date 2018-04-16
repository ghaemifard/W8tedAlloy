W8tedAlloy
===========


This repository is a version of Alloy that allows you write constraints which are in conflict with each other,
using a MaxSAT solver to find an optimal model.

### Changes

The most important change is adding the keyword 'odds' to the Alloy specifications.

Usage:

    odds 2 allBooksHaveSomePage{...}

To work properly, it is essential to choose a MaxSAT solver as your solver, otherwise the code above will be translated as:

    pred allBooksHaveSomePage{...}
    
### Download

The jar file is located in the folder 'dist'. You can simply run W8tedAlloy as follows:

    java -jar W8tedAlloy.jar
    
