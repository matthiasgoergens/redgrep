class (CutI cut, AltI alt) => Alt r where
    alt :: r f s -> r f' s' -> r (cut f f') (alt s s')
