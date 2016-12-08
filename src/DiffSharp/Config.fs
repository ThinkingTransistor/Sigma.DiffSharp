//
// This file is part of
// DiffSharp: Differentiable Functional Programming
//
// Copyright (c) 2014--2016, National University of Ireland Maynooth (Atilim Gunes Baydin, Barak A. Pearlmutter)
// 
// Released under the LGPL license.
//
//   DiffSharp is free software: you can redistribute it and/or modify
//   it under the terms of the GNU Lesser General Public License as published by
//   the Free Software Foundation, either version 3 of the License, or
//   (at your option) any later version.
//
//   DiffSharp is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
//   GNU General Public License for more details.
//
//   You should have received a copy of the GNU Lesser General Public License
//   along with DiffSharp. If not, see <http://www.gnu.org/licenses/>.
//
// Written by:
//
//   Atilim Gunes Baydin
//   atilimgunes.baydin@nuim.ie
//
//   Barak A. Pearlmutter
//   barak@cs.nuim.ie
//
//   Brain and Computation Lab
//   Hamilton Institute & Department of Computer Science
//   National University of Ireland Maynooth
//   Maynooth, Co. Kildare
//   Ireland
//
//   www.bcl.hamilton.ie
//

namespace DiffSharp.Config

open DiffSharp.Backend

/// 
type BackendConfig<'T> = 
    { BackendHandle : Backend<'T>
      Epsilon : 'T
      EpsilonRec : 'T
      EpsilonRec2 : 'T
      FixedPointEpsilon : 'T
      FixedPointMaxIterations: int
      VisualisationContrast : 'T }

/// A backend provier which selects a backend based on the given object (D, DV, DM; for dynamic/multithreaded backends)
type IBackendProvider =
    abstract member GetBackend<'T> : obj -> BackendConfig<'T> 

/// Record type holding configuration parameters
type Config =
    {BackendConfigFloat32 : BackendConfig<float32>
     BackendConfigFloat64 : BackendConfig<float>
     GrayscalePalette : string[]}

/// Global configuration
type GlobalConfig() =
    static let GrayscalePaletteUnicode = [|" "; "·"; "-"; "▴"; "▪"; "●"; "♦"; "■"; "█"|]
    static let GrayscalePaletteASCII = [|" "; "."; ":"; "x"; "T"; "Y"; "V"; "X"; "H"; "N"; "M"|]
    static let mutable C =
        let eps = 0.00001
        let fpeps = 0.01
        {BackendConfigFloat32 = {   BackendHandle = OpenBLAS.Float32Backend()
                                    Epsilon = float32 eps 
                                    EpsilonRec = 1.f / (float32 eps)
                                    EpsilonRec2 = 0.5f / (float32 eps) 
                                    FixedPointEpsilon = float32 fpeps
                                    FixedPointMaxIterations = 100 
                                    VisualisationContrast = 1.2f}
         BackendConfigFloat64 = {   BackendHandle = OpenBLAS.Float64Backend()
                                    Epsilon = float eps 
                                    EpsilonRec = 1. / (float eps)
                                    EpsilonRec2 = 0.5 / (float eps) 
                                    FixedPointEpsilon = float fpeps
                                    FixedPointMaxIterations = 100 
                                    VisualisationContrast = 1.2}
         GrayscalePalette = GrayscalePaletteASCII}

    static member BackendProvider : IBackendProvider = DefaultBackendProvider() :> IBackendProvider
    static member Float32BackendConfig = C.BackendConfigFloat32
    static member Float64BackendConfig = C.BackendConfigFloat64
    static member Float32Backend = C.BackendConfigFloat32.BackendHandle
    static member Float64Backend = C.BackendConfigFloat64.BackendHandle
    static member Float32Epsilon = C.BackendConfigFloat32.Epsilon
    static member Float64Epsilon = C.BackendConfigFloat64.Epsilon
    static member Float32EpsilonRec = C.BackendConfigFloat32.EpsilonRec
    static member Float64EpsilonRec = C.BackendConfigFloat64.EpsilonRec
    static member Float32EpsilonRec2 = C.BackendConfigFloat32.EpsilonRec2
    static member Float64EpsilonRec2 = C.BackendConfigFloat64.EpsilonRec2
    static member Float32FixedPointEpsilon = C.BackendConfigFloat32.FixedPointEpsilon
    static member Float64FixedPointEpsilon = C.BackendConfigFloat64.FixedPointEpsilon
    static member FixedPointMaxIterations = C.BackendConfigFloat32.FixedPointMaxIterations
    static member Float32VisualizationContrast = C.BackendConfigFloat32.VisualisationContrast
    static member Float64VisualizationContrast = C.BackendConfigFloat64.VisualisationContrast
    static member GrayscalePalette = C.GrayscalePalette
    static member SetDefaultBackend(backend:string) =
        match backend with
        | "OpenBLAS" ->
            C <- {C with
                    BackendConfigFloat32 = { C.BackendConfigFloat32 with BackendHandle = OpenBLAS.Float32Backend() }
                    BackendConfigFloat64 = { C.BackendConfigFloat64 with BackendHandle = OpenBLAS.Float64Backend() }
                   }
        | _ -> invalidArg "" "Unsupported backend. Try: OpenBLAS"

and DefaultBackendProvider() = 
    static let float32type = typeof<float32>
    static let float64type = typeof<float>
    
    interface IBackendProvider with
        member b.GetBackend<'T> value =
           match typeof<'T> with
           | x when x = float32type -> (GlobalConfig.Float64BackendConfig :> obj) :?> BackendConfig<'T>
           | x when x = float64type -> (GlobalConfig.Float32BackendConfig :> obj) :?> BackendConfig<'T>
           | _ -> invalidArg "" "Unsupported type, try float32 or float"