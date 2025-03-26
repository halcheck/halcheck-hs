module Demo.TestShrinking (tests) where

import Data.Default
import Test.Tasty
import Test.Tasty.Falsify

import qualified Test.Falsify.Generator as Gen
import qualified Test.Falsify.Predicate as P

tests :: TestTree
tests = testGroup "Demo.TestShrinking" [
      testProperty                   "prim" prop_prim
    , testPropertyWith expectFailure "mod1" prop_mod1
    , testProperty                   "mod2" prop_mod2
    ]
  where
    expectFailure :: TestOptions
    expectFailure = def { expectFailure = ExpectFailure }

prop_prim :: Property ()
prop_prim =
    testShrinkingOfGen P.ge $
      Gen.prim

prop_mod1 :: Property ()
prop_mod1 =
    testShrinkingOfGen P.ge $
      (`mod` 100) <$> Gen.prim

-- The test will result in a test failure
--
-- We should see in the log both the value generated by @Gen.prim@, as well as
-- the result. Note that the fmap is on the /outside/ now.
prop_mod2 :: Property ()
prop_mod2 =
    testShrinking P.ge $ do
      x <- (`mod` 100) <$> gen Gen.prim
      testFailed x


