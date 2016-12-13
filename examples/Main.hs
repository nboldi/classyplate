{-# LANGUAGE TypeApplications, FlexibleContexts, RankNTypes, DataKinds, LambdaCase, ScopedTypeVariables, ConstraintKinds, AllowAmbiguousTypes #-}

module Main where

import MiniLangExample

import Data.Generics.ClassyPlate
import Example

import DirectUni (directUni1, directUni2)
import AutoUni (autoUni1, autoUni2)

import Generate

import Criterion.Main

our1 d = bottomUp @(MonoMatch D) (monoApp testFun1) (generateA d)
our2 d = bottomUp @(MonoMatch C) (monoApp testFun2) (generateA d)
auto1 d = smartTraverse @(MonoMatch D) (monoApp testFun1) (generateA d)
auto2 d = smartTraverse @(MonoMatch C) (monoApp testFun2) (generateA d)

topDown1 d = topDown @(MonoMatch D) (monoApp testFun1) (generateA d)
topDown2 d = topDown @(MonoMatch C) (monoApp testFun2) (generateA d)
topDownSelective1 d = selectiveTraverse @(MonoMatch D) (\e -> (monoApp testFun1 e, True)) (generateA d)
topDownSelective2 d = selectiveTraverse @(MonoMatch C) (\e -> (monoApp testFun2 e, True)) (generateA d)

bottomUp1 d = bottomUpTrav @(MonoMatch D) (monoApp testFun1) (generateA d)
bottomUp2 d = bottomUpTrav @(MonoMatch C) (monoApp testFun2) (generateA d)


main = defaultMain
  [ bgroup "generation" 
    [ bench "61" $ nf generateA 61
    , bench "101" $ nf generateA 101
    , bench "141" $ nf generateA 141
    ]
  , bgroup "our"
    [ bgroup "deep" 
        [ bench "61" $ nf our1 61
        , bench "101" $ nf our1 101
        , bench "141" $ nf our1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf our2 61
        , bench "101" $ nf our2 101
        , bench "141" $ nf our2 141]
    ]
  , bgroup "topdown"
    [ bgroup "deep" 
        [ bench "61" $ nf topDown1 61
        , bench "101" $ nf topDown1 101
        , bench "141" $ nf topDown1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf topDown2 61
        , bench "101" $ nf topDown2 101
        , bench "141" $ nf topDown2 141]
    ]
  , bgroup "selective"
    [ bgroup "deep" 
        [ bench "61" $ nf topDownSelective1 61
        , bench "101" $ nf topDownSelective1 101
        , bench "141" $ nf topDownSelective1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf topDownSelective2 61
        , bench "101" $ nf topDownSelective2 101
        , bench "141" $ nf topDownSelective2 141]
    ]
  , bgroup "bottomUp-desc"
    [ bgroup "deep" 
        [ bench "61" $ nf bottomUp1 61
        , bench "101" $ nf bottomUp1 101
        , bench "141" $ nf bottomUp1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf bottomUp2 61
        , bench "101" $ nf bottomUp2 101
        , bench "141" $ nf bottomUp2 141]
    ]
  , bgroup "auto"
    [ bgroup "deep" 
        [ bench "61" $ nf auto1 61
        , bench "101" $ nf auto1 101
        , bench "141" $ nf auto1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf auto2 61
        , bench "101" $ nf auto2 101
        , bench "141" $ nf auto2 141]
    ]
  , bgroup "autoUni" 
    [ bgroup "deep" 
        [ bench "61" $ nf autoUni1 61
        , bench "101" $ nf autoUni1 101
        , bench "141" $ nf autoUni1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf autoUni2 61
        , bench "101" $ nf autoUni2 101
        , bench "141" $ nf autoUni2 141]
    ]
  , bgroup "directUni" 
    [ bgroup "deep" 
        [ bench "61" $ nf directUni1 61
        , bench "101" $ nf directUni1 101
        , bench "141" $ nf directUni1 141]
    , bgroup "shallow" 
        [ bench "61" $ nf directUni2 61
        , bench "101" $ nf directUni2 101
        , bench "141" $ nf directUni2 141]
    ]
  ]