{-# LANGUAGE DataKinds, RequiredTypeArguments, TypeFamilies #-}

import Data.Kind

data Attr = Attr1 | Attr2

type family AttrValue (a :: Attr) :: Type
type instance AttrValue Attr1 = Bool
type instance AttrValue Attr2 = Int

getAttr :: forall (a :: Attr) -> AttrValue a
getAttr Attr1 = False
getAttr Attr2 = 0
