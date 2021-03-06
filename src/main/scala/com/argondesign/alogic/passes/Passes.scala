////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Driver to apply all compiler passes to trees
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.Trees.Arg
import com.argondesign.alogic.backend.CodeGeneration
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Source

import scala.util.ChainingSyntax

object Passes extends ChainingSyntax {

  // All trees are transformed with the given pass before the next pass begins
  def apply(
      source: Source,
      loc: Loc,
      params: List[Arg]
    )(
      implicit
      cc: CompilerContext
    ): Unit = {
    // Define the passes to apply
    val passes =
      ////////////////////////////////////////////////////////////////////////
      // Front-end
      ////////////////////////////////////////////////////////////////////////
      FrontendPass andThen
        MarkTopLevels andThen
        DropPackageAndParametrizedDescs andThen
        DescToDeclDefn andThen
        ////////////////////////////////////////////////////////////////////////
        // Middle-end
        ////////////////////////////////////////////////////////////////////////
        Desugar andThen
        Fold andThen
        NormalizeFunctions andThen
        InlineMethods andThen
        NormalizeReferences() andThen
        PortCheck andThen
        LowerPipeline andThen
        ExtractTypes andThen
        LowerLoops andThen
        NormalizeControl andThen
        AnalyseCallGraph andThen
        ConvertCtrlFuncArgret andThen
        ConvertCtrlFuncLocals andThen
        RemoveStructuralSharing andThen
        ConvertControl andThen
        SimplifyStates andThen
        CreateStateSystem andThen
        Replace1Stacks andThen
        // TODO: Replace1Arrays
        DefaultStorage andThen
        LowerFlowControl() andThen
        LowerSrams() andThen
        LowerStacks andThen
        LowerRegPorts andThen
        LiftSrams andThen
        AddClockAndReset() andThen
        LowerAssertions andThen
        LowerForeignFunctions() andThen
        LowerArrays andThen
        SplitStructs() andThen
        LowerVectors() andThen
        // FIXME: AddCasts andThen // TODO: Remove the need for this (make previous passes not add Nums..)
        Fold andThen
        SimplifyCat andThen
        ////////////////////////////////////////////////////////////////////////
        // Back-end
        ////////////////////////////////////////////////////////////////////////
        RenameSymbols(last = false) andThen
        LowerVariables andThen
        LowerInterconnect andThen
        InferImplications andThen
        PropagateImplications andThen
        RemoveStructuralSharing andThen
        InlineKnownVars(combOnly = true) andThen
        Fold andThen
        OptimizeClearOnStall andThen
        LowerWait andThen
        RemoveAssume andThen
        DefaultAssignments andThen
        TieOffInputs andThen
        InlineKnownVars(combOnly = false) andThen
        Fold andThen
        RemoveUnused andThen
        Fold andThen
        InterconnectCheck andThen
        CreateTemporaries andThen
        RenameSymbols(last = true) andThen
        WriteAux andThen
        CodeGeneration

    // Apply the passes to the input
    passes((source, loc, params))
  }

}
