{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main (
  main,
) where

import Protolude

import Test.Tasty
import Test.Tasty.HUnit as HU
import Test.Tasty.QuickCheck
import Test.QuickCheck.Monadic as QM

import Example (micpWrapper, micpComponents)

import Pedersen
import PrimeField

suite :: TestTree
suite = testGroup "Test Suite" [
    testGroup "Units"
      [ pedersenTests
      , micpTests
      ]
  ]

pedersenTests :: TestTree
pedersenTests = testGroup "Pedersen Commitment Scheme"
  [ localOption (QuickCheckTests 50) $
      testProperty "x == Open(Commit(x),r)" $ monadicIO $ do
        (a, cp) <- liftIO $ setup 256
        x <- liftIO $ randomInZq $ pedersenSPF cp
        pc <- liftIO $ commit x cp
        QM.assert $ open cp (commitment pc) (reveal pc)

  , testCaseSteps "Additive Homomorphic Commitments" $ \step -> do
      step "Generating commit params..."
      (a,cp) <- setup 256
      let spf = pedersenSPF cp

      step "Generating two random nums in Zp to commit."
      x <- randomInZq spf
      y <- randomInZq spf

      step "Commit the two random nums."
      px@(Pedersen cx rx) <- commit x cp
      py@(Pedersen cy ry) <- commit y cp

      step "Check the validity of the commitments"
      assertBool "Pedersen commitments failed." $
        open cp cx rx && open cp cy ry

      step "Verify that homomorphic addition of commitments works"
      let cyz = homoAdd cp cx cy
      let pyz = verifyHomoAdd cp px py
      assertBool "Additive homomorphic property doesn't hold." $
        cyz == commitment pyz

      putText "Starting example:"
  ]

micpTests :: TestTree
micpTests = testGroup "Mutually Independent Commitment Protocol"
  [ testCase "Testing MICP Components" $
      assertBool "MICP Components test failed!" =<< micpComponents 256
  , testCase "Testing MICP Wrapper" $ 
      assertBool "MICP Wrapper test failed!" =<< micpWrapper 256
  ]

main :: IO ()
main = defaultMain suite
