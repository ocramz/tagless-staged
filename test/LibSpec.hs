module LibSpec where

import Test.Hspec

import Lib (runR, exS1)

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "Lib" $ do
    it "works" $ do
      runR exS1 `shouldBe` 3
