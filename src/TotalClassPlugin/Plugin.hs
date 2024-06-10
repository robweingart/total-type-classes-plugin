module TotalClassPlugin.Plugin ( plugin ) where

import GHC.Plugins

import TotalClassPlugin.Rewriter (totalTcResultAction)
import TotalClassPlugin.Solver (totalTcPlugin)

plugin :: Plugin
plugin = defaultPlugin
  { typeCheckResultAction = totalTcResultAction
  , tcPlugin = totalTcPlugin
  }
