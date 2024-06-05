module TestPlugin.Plugin ( plugin ) where

import GHC.Plugins

import TestPlugin.Rewriter (totalTcResultAction)
import TestPlugin.Solver (totalTcPlugin)

plugin :: Plugin
plugin = defaultPlugin
  { typeCheckResultAction = totalTcResultAction
  , tcPlugin = totalTcPlugin
  }
