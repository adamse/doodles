-- |
module Bi.Ex where

import Prelude

import Bi.Syn
import Bi.Bi
import Bi.Tc

type Term' = Term Integer Integer
type Typ' = Typ Integer

idTerm :: Term'
idTerm = lam 1 (V 1)

idTyp :: Typ'
idTyp = fall 1 (TV 1 :-> TV 1)

idTyp' :: Typ'
idTyp' = One :-> One

checks@[idCheck, idCheck', unitCheck, idAppCheck] = map runTc'
  [ check idTerm idTyp
  , check idTerm idTyp'
  , check Unit One
  , check (idTerm :@ Unit) One
  ]

test = all (== Right ()) $ map fst checks
