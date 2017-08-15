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
namespace DiffSharp.Backend

open DiffSharp.Util

type MapOp = 
    | Mul
    | Div
    | Add
    | Sub
    | Pow_Ab
    | Pow_Ba
    | Atan2_Ab
    | Atan2_Ba
    | Log
    | Log10
    | Exp
    | Sin
    | Cos
    | Tan
    | Sqrt
    | Sinh
    | Cosh
    | Tanh
    | Asin
    | Acos
    | Atan
    | Abs
    | Sign
    | Floor
    | Ceiling
    | Round
    | ReL
    | Sigmoid

/// Interface for DiffSharp backends
[<AllowNullLiteral>]
type Backend<'T> = 
    // Create buffer
    abstract CreateDataBuffer : 'T [] -> ISigmaDiffDataBuffer<'T>
    abstract CreateUninitialisedArray : int -> 'T []
    abstract CreateZeroArray : int -> 'T []
    abstract CreateValueArray : int * 'T -> 'T []
    // Scalar valued
    abstract Mul_Dot_V_V : ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T> -> 'T
    abstract L1Norm_V : ISigmaDiffDataBuffer<'T> -> 'T
    abstract L2Norm_V : ISigmaDiffDataBuffer<'T> -> 'T
    abstract SupNorm_V : ISigmaDiffDataBuffer<'T> -> 'T
    abstract Sum_V : ISigmaDiffDataBuffer<'T> -> 'T
    abstract Sum_M : ISigmaDiffDataBuffer<'T> -> 'T
    abstract MaxIndex_V : ISigmaDiffDataBuffer<'T> -> int
    abstract MinIndex_V : ISigmaDiffDataBuffer<'T> -> int
    // Vector valued
    abstract Add_V_V : ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Add_V_V_InPlace : ISigmaDiffDataBuffer<'T> * int * ISigmaDiffDataBuffer<'T> * int * int
     -> ISigmaDiffDataBuffer<'T>
    abstract Add_S_V : 'T * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Sub_V_V : ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Sub_S_V : 'T * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Sub_V_S : ISigmaDiffDataBuffer<'T> * 'T -> ISigmaDiffDataBuffer<'T>
    abstract Mul_S_V : 'T * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Mul_M_V : ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Mul_M_V_Add_V : ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T>
     -> ISigmaDiffDataBuffer<'T>
    abstract Mul_V_M : ISigmaDiffDataBuffer<'T> * ShapedDataBufferView<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Solve_M_V : ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T> option
    abstract SolveSymmetric_M_V : ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T> option
    abstract Diagonal_M : ShapedDataBufferView<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Map_F_V : MapOp * ('T -> 'T) * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Map_F_S_V : 'T * MapOp * ('T -> 'T) * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Map2_F_V_V : MapOp * ('T -> 'T -> 'T) * ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T>
     -> ISigmaDiffDataBuffer<'T>
    abstract ReshapeCopy_MRows_V : ShapedDataBufferView<'T> -> ISigmaDiffDataBuffer<'T>
    // Matrix valued
    abstract Mul_Out_V_V : ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract Add_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Add_M_M_InPlace : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Add_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Add_V_MCols : ISigmaDiffDataBuffer<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Sub_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Sub_M_S : ShapedDataBufferView<'T> * 'T -> ShapedDataBufferView<'T>
    abstract Sub_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_M_M_Add_V_MCols : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T>
     -> ShapedDataBufferView<'T>
    abstract Add_M_Colwise_V_InPlace : ShapedDataBufferView<'T> * ISigmaDiffDataBuffer<'T> -> ISigmaDiffDataBuffer<'T>
    abstract Mul_Had_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Inverse_M : ShapedDataBufferView<'T> -> ShapedDataBufferView<'T> option
    abstract Det_M : ShapedDataBufferView<'T> -> 'T option
    abstract Transpose_M : ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Permute_M : ShapedDataBufferView<'T> * int [] -> ShapedDataBufferView<'T>
    abstract Reshape_M : ShapedDataBufferView<'T> * int64 [] -> ShapedDataBufferView<'T>
    abstract Map_F_M : MapOp * ('T -> 'T) * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Map_F_S_M : 'T * MapOp * ('T -> 'T) * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Map2_F_M_M : MapOp * ('T -> 'T -> 'T) * ShapedDataBufferView<'T> * ShapedDataBufferView<'T>
     -> ShapedDataBufferView<'T>
    abstract ReshapeCopy_V_MRows : int * ISigmaDiffDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract RepeatReshapeCopy_V_MRows : int * ISigmaDiffDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract RepeatReshapeCopy_V_MCols : int * ISigmaDiffDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract CustomOp_DM_Forward : ShapedDataBufferView<'T> * obj -> ShapedDataBufferView<'T>
    abstract CustomOp_DM_Backward : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> * ShapedDataBufferView<'T> * obj
     -> ShapedDataBufferView<'T>

     // TODO custom DV ops not yet supported, still testing custom DM ops
//    abstract CustomOp_DV_Forward : ISigmaDiffDataBuffer<'T> * obj -> ISigmaDiffDataBuffer<'T>
//    abstract CustomOp_DV_Backward : ISigmaDiffDataBuffer<'T> * ISigmaDiffDataBuffer<'T> * obj
//     -> ISigmaDiffDataBuffer<'T>
