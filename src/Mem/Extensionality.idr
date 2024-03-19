module Mem.Extensionality

import public Control.Relation

infix 5 -=-

public export
data (-=-) : (f, g : a -> b) -> Type where
    Ext : ((x : a) -> f x = g x) -> f -=- g

public export
Symmetric (a -> b) (-=-) where
    symmetric (Ext p) = Ext $ \x => sym (p x)

public export
Transitive (a -> b) (-=-) where
    transitive (Ext p1) (Ext p2) = Ext $ \x => trans (p1 x) (p2 x)
