(**********************************************************************
* Taci                                                                *
* Copyright (C) 2007-2008 Zach Snow, David Baelde, Alexandre Viel     *
*                                                                     *
* This program is free software; you can redistribute it and/or modify*
* it under the terms of the GNU General Public License as published by*
* the Free Software Foundation; either version 2 of the License, or   *
* (at your option) any later version.                                 *
*                                                                     *
* This program is distributed in the hope that it will be useful,     *
* but WITHOUT ANY WARRANTY; without even the implied warranty of      *
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *
* GNU General Public License for more details.                        *
*                                                                     *
* You should have received a copy of the GNU General Public License   *
* along with this code; if not, write to the Free Software Foundation,*
* Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA        *
**********************************************************************)

(********************************************************************
*Tacticals:
* A functor that constructs a module containing all of the firstorder
* logic's tacticals.
********************************************************************)
module Tacticals :
  functor (Param : Firstordertypes.ParamSig) ->
  functor (FOT : Firstordertypes.TypesSig) ->
  functor (O : Output.Output) ->
sig
  type tactic = (FOT.sequent, FOT.proof) Logic.tactic
  type tactical = (FOT.session, tactic) Logic.tactical
  
  val genericTacticals : tactical Logic.table
  
  val orElseTactical : tactical -> tactical -> tactical
  
  val admitTactical : tactical
  val andL : tactical
  val andR : tactical
  val orL : tactical
  val orR : tactical
  val orLeft : tactical
  val orRight : tactical
  
  val impL : tactical
  val impR : tactical
  
  val piL : tactical
  val piR : tactical
  
  val sigmaL : tactical
  val sigmaR : tactical
  
  val nablaL : tactical
  val nablaR : tactical
  
  val eqL : tactical
  val eqR : tactical
  val axiom : tactical
  
  val muL : tactical
  val muR : tactical
  val nuL : tactical
  val nuR : tactical
  
  val inductionTactical : tactical
  val coinductionTactical : tactical
  
  val weakL : tactical
  val weakR : tactical
  val contractL : tactical
  val contractR : tactical
  val rotateR : tactical
  val rotateL : tactical

  val examineTactical : tactical
  val examinePatternTactical : tactical
  
  val simplifyTactical : tactical
  
  val trueR : tactical
  val falseL : tactical
  
  val applyTactical : tactical
  val cutTactical : tactical
  val cutLemmaTactical : tactical
  val forceTactical : tactical
  val iterativeDeepeningProveTactical : tactical
  val asyncTactical : tactical
  
  val abstractTactical : tactical
  val focusTactical : tactical
  val focusRightTactical : tactical
  val freezeTactical : tactical
  val unfocusTactical : tactical
  val syncStepTactical : tactical
  
  val setBoundTactical : tactical
  
  val casesTactical : tactical
  val introsTactical : tactical
end
