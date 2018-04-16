W8tedAlloy
===========


This repository is a version of Alloy that allows you write constraints which are in conflict with each other,
using a MaxSAT solver to find an optimal model.

### Changes

The most important change is adding the keyword 'odds' to the Alloy specifications. It can define a constraint with prioritiy levels 1 to 9.

Usage:

    odds 2 allBooksHaveSomePages{...}

To work properly, it is essential to choose a MaxSAT solver as your solver, otherwise the code above will be translated as:

    pred allBooksHaveSomePages{...}
    
### Download

The jar file is located in the folder 'dist'. You can simply run W8tedAlloy as follows:

    java -jar W8tedAlloy.jar
    
### Example

    sig Book{ content:  Page }

    sig Page{}

    one sig Abstract1 extends Page{}
    one sig Abstract2 extends Page{}
    one sig HardBook1 extends Book{}
    one sig HardBook2 extends Book{}

 
    odds 5  lowPriority{ 
        all b : Book | some b.content
    }

    pred aMust {
        HardBook1.content = none
    }
    run {aMust  and lowPriority } for 6 but exactly 4 Book

    
