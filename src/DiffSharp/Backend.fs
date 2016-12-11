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

/// Interface for DiffSharp backends
[<AllowNullLiteral>]
type Backend<'T> = 
    // Create buffer
    abstract CreateDataBuffer : 'T [] -> IDataBuffer<'T>
    // Scalar valued
    abstract Mul_Dot_V_V : IDataBuffer<'T> * IDataBuffer<'T> -> 'T
    abstract L1Norm_V : IDataBuffer<'T> -> 'T
    abstract L2Norm_V : IDataBuffer<'T> -> 'T
    abstract SupNorm_V : IDataBuffer<'T> -> 'T
    abstract Sum_V : IDataBuffer<'T> -> 'T
    abstract Sum_M : IDataBuffer<'T> -> 'T
    // Vector valued
    abstract Add_V_V : IDataBuffer<'T> * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Add_S_V : 'T * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Sub_V_V : IDataBuffer<'T> * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Sub_S_V : 'T * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Sub_V_S : IDataBuffer<'T> * 'T -> IDataBuffer<'T>
    abstract Mul_S_V : 'T * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Mul_M_V : ShapedDataBufferView<'T> * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Mul_M_V_Add_V : ShapedDataBufferView<'T> * IDataBuffer<'T> * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Mul_V_M : IDataBuffer<'T> * ShapedDataBufferView<'T> -> IDataBuffer<'T>
    abstract Solve_M_V : ShapedDataBufferView<'T> * IDataBuffer<'T> -> IDataBuffer<'T> option
    abstract SolveSymmetric_M_V : ShapedDataBufferView<'T> * IDataBuffer<'T> -> IDataBuffer<'T> option
    abstract Diagonal_M : ShapedDataBufferView<'T> -> IDataBuffer<'T>
    abstract Map_F_V : ('T -> 'T) * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract Map2_F_V_V : ('T -> 'T -> 'T) * IDataBuffer<'T> * IDataBuffer<'T> -> IDataBuffer<'T>
    abstract ReshapeCopy_MRows_V : ShapedDataBufferView<'T> -> IDataBuffer<'T>
    // Matrix valued
    abstract Mul_Out_V_V : IDataBuffer<'T> * IDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract Add_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Add_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Add_V_MCols : IDataBuffer<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Sub_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Sub_M_S : ShapedDataBufferView<'T> * 'T -> ShapedDataBufferView<'T>
    abstract Sub_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_S_M : 'T * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Mul_M_M_Add_V_MCols : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> * IDataBuffer<'T>
     -> ShapedDataBufferView<'T>
    abstract Mul_Had_M_M : ShapedDataBufferView<'T> * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Inverse_M : ShapedDataBufferView<'T> -> ShapedDataBufferView<'T> option
    abstract Det_M : ShapedDataBufferView<'T> -> 'T option
    abstract Transpose_M : ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Map_F_M : ('T -> 'T) * ShapedDataBufferView<'T> -> ShapedDataBufferView<'T>
    abstract Map2_F_M_M : ('T -> 'T -> 'T) * ShapedDataBufferView<'T> * ShapedDataBufferView<'T>
     -> ShapedDataBufferView<'T>
    abstract ReshapeCopy_V_MRows : int * IDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract RepeatReshapeCopy_V_MRows : int * IDataBuffer<'T> -> ShapedDataBufferView<'T>
    abstract RepeatReshapeCopy_V_MCols : int * IDataBuffer<'T> -> ShapedDataBufferView<'T>
