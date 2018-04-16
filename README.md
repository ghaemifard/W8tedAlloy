Hello Everyone!

W8tedAlloy is a version of Alloy, that allows you write constraints which are in conflict with each other,
using a MaxSAT solver to find an optimal model.

The most important change is adding the keyword 'odds' to the Alloy specifications.
Usage:
    odds 2 allBooksHaveSomePage{...}

To work properly, it is essential to choose a MaxSAT solver as your solver, otherwise the code above will be translated as:
    pred allBooksHaveSomePage{...}
    
    
    
    
