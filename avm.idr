-- Unification of features structures (for unification grammars).

module Main

-- Attributes form a closed set.

data Attribute = A | B | C | D

-- The concept of deriving interfaces doesn't exists in Idris.
-- We could use elaborator reflection but at this stage let's just handcode the Show and Eq implementations.

Show Attribute where
    show A = "A"
    show B = "B"
    show C = "C"
    show D = "D"

Eq Attribute where
    A == A = True
    B == B = True
    C == C = True
    D == D = True
    _ == _ = False

mutual

-- Unifiable - values that can be unified

    data Unifiable = UString String | UInteger Integer | UAVM AVM

    desc_unif : Unifiable -> String
    desc_unif x = case x of
                UString s   => s
                UInteger n  => show n
                UAVM avm    => desc_avm avm

-- AVM - recursive features structures

    record AVM where
        constructor MkAVM
        features : List (Attribute, Unifiable)
    
    add : Attribute -> Unifiable -> AVM -> AVM
    add attr value avm = MkAVM ((attr, value) :: avm.features)

    desc_avm_features : List (Attribute, Unifiable) -> String
    desc_avm_features Nil = ""
    desc_avm_features ((attr, value) :: xs) = (show attr) ++ ":" ++ (desc_unif value) ++ " " ++ (desc_avm_features xs)
    
    desc_avm : AVM -> String
    desc_avm avm = "[ " ++ (desc_avm_features avm.features) ++ "]"

    equals : Unifiable -> Unifiable -> Bool
    equals (UString s1) (UString s2) = s1 == s2
    equals (UInteger n1) (UInteger n2) = n1 == n2
    equals (UAVM avm1) (UAVM avm2) = avm_is_identical_list avm1.features avm2.features
    equals _ _ = False

    avm_is_identical_list : List (Attribute, Unifiable) -> List (Attribute, Unifiable) -> Bool
    avm_is_identical_list [] [] = True
    avm_is_identical_list (_ :: _) [] = False
    avm_is_identical_list [] (_ :: _) = False
    avm_is_identical_list ((attr1, value1) :: xs) ((attr2, value2) :: ys) =
        if (attr1 == attr2 && equals value1 value2) then avm_is_identical_list xs ys else False
    
avm_extract_attr : Attribute -> (List (Attribute, Unifiable)) -> Maybe (Unifiable, List (Attribute, Unifiable))
avm_extract_attr _ [] = Nothing
avm_extract_attr attr1 ((attr2, value1) :: tail) =
    if (attr1 == attr2) then Just (value1, tail)
    else case avm_extract_attr attr1 tail of
        Just (value2, rest) => Just (value2, (attr2, value1) :: rest)
        _ => Nothing

is_string : Unifiable -> Bool
is_string x = case x of
                UString _   => True
                _           => False

is_integer : Unifiable -> Bool
is_integer x = case x of
                UInteger _  => True
                _           => False

is_avm : Unifiable -> Bool
is_avm x = case x of
                UAVM _  => True
                _       => False

mutual

    -- a recursive unification procedure inspired by the classical Prolog implementation 
    unify : Unifiable -> Unifiable -> Maybe Unifiable
    unify term1 term2 =
        case term1 of
            UString s1 =>
                case term2 of
                    UString s2 => if (s1 == s2) then Just (UString s1) else Nothing
                    _ => Nothing
            UInteger n1 =>
                case term2 of
                    UInteger n2 => if (n1 == n2) then Just (UInteger n1) else Nothing
                    _ => Nothing
            UAVM avm1 =>
                case term2 of
                    UAVM avm2 =>
                        case unify_avm_features avm1.features avm2.features of
                            Just list => Just (UAVM (MkAVM list))
                            _ => Nothing
                    _ => Nothing

    unify_avm_features : List (Attribute, Unifiable) -> List (Attribute, Unifiable) -> Maybe (List (Attribute, Unifiable))
    unify_avm_features list1 list2 =
        if (avm_is_identical_list list1 list2) then Just list1
        else unify_avm_features_recurse list1 list2

    unify_avm_features_recurse : List (Attribute, Unifiable) -> List (Attribute, Unifiable) -> Maybe (List (Attribute, Unifiable))
    unify_avm_features_recurse list [] = Just list
    unify_avm_features_recurse [] list = Just list
    unify_avm_features_recurse ((attr, value1) :: rest1) list2 =
        case avm_extract_attr attr list2 of
            Just (value2, rest2) =>
                case unify value1 value2 of
                    Just value =>
                        case unify_avm_features rest1 rest2 of
                            Just rest => Just ((attr, value) :: rest)
                            _ => Nothing 
                    _ => Nothing
            _ =>
                case unify_avm_features rest1 list2 of
                    Just rest => Just ((attr, value1) :: rest)
                    _ => Nothing 

-- Main function - for testing

main : IO ()
main = do
        let avm1 = MkAVM [] ;
        let avm1 = add A (UString "_a_") avm1 ;
        let avm1 = add B (UString "_b_") avm1 ;
        let avm1 = add C (UString "_c_") avm1 ;
        putStrLn $ desc_avm avm1 ;
        let avm2 = MkAVM [] ;
        let avm2 = add C (UString "_c_") avm2 ;
        let avm2 = add B (UString "_b_") avm2 ;
        let avm2 = add A (UString "_a_") avm2 ;
        putStrLn $ desc_avm avm2 ;
        case unify (UAVM avm1) (UAVM avm2) of
            Just avm => putStrLn $ "unified: " ++ (desc_unif avm)
            _ => putStrLn "not unifiable"
