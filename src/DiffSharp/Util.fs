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
/// Various utility functions
module DiffSharp.Util

open System.Threading.Tasks
open System

/// Gets the first term of a 3-tuple
let inline fst3 (f, _, _) = f

/// Gets the second term of a 3-tuple
let inline snd3 (_, s, _) = s

/// Gets the tail of a 3-tuple
let inline trd (_, _, t) = t

/// Gets the first and third terms of a 3-tuple
let inline fsttrd (f, _, t) = (f, t)

/// Gets the second and third terms of a 3-tuple
let inline sndtrd (_, s, t) = (s, t)

/// Value of log 10.
let log10ValFloat64 = log 10.

let log10ValFloat32 = log 10.f

/// Computes a combined hash code for the objects in array `o`
let inline hash (o : obj []) = Array.map (fun a -> a.GetHashCode()) o |> Seq.fold (fun acc elem -> acc * 23 + elem) 17

/// Gets an array of size `n`, where the `i`-th element is 1 and the rest of the elements are zero
let inline standardBasis (n : int) (i : int) = 
    let s = Array.zeroCreate n
    s.[i] <- LanguagePrimitives.GenericOne
    s

/// Gets an array of size `n`, where the `i`-th element has value `v` and the rest of the elements are zero
let inline standardBasisVal (n : int) (i : int) v = 
    let s = Array.zeroCreate n
    s.[i] <- v
    s

/// Copies the upper triangular elements of the square matrix given in the 2d array `m` to the lower triangular part
let inline copyUpperToLower (m : _ [,]) = 
    if (Array2D.length1 m) <> (Array2D.length2 m) then invalidArg "" "Expecting a square matrix."
    let r = Array2D.copy m
    let rows = r.GetLength 0
    if rows > 1 then 
        Parallel.For(1, rows, fun i -> Parallel.For(0, i, fun j -> r.[i, j] <- r.[j, i]) |> ignore) |> ignore
    r

let inline signummod x = 
    if x < LanguagePrimitives.GenericZero then -LanguagePrimitives.GenericOne
    elif x > LanguagePrimitives.GenericZero then LanguagePrimitives.GenericOne
    else LanguagePrimitives.GenericZero

let inline signum (x : 'a) = (^a : (static member Sign : ^a -> ^a) x)
let inline logsumexp (x : ^a) = (^a : (static member LogSumExp : ^a -> ^b) x)
let inline softplus (x : ^a) = (^a : (static member SoftPlus : ^a -> ^a) x)
let inline softsign (x : ^a) = (^a : (static member SoftSign : ^a -> ^a) x)
let inline sigmoid (x : ^a) = (^a : (static member Sigmoid : ^a -> ^a) x)
let inline reLU (x : ^a) = (^a : (static member ReLU : ^a -> ^a) x)
let inline softmax (x : ^a) = (^a : (static member SoftMax : ^a -> ^a) x)
let inline maximum (x : ^a) (y : ^b) : ^c = ((^a or ^b) : (static member Max : ^a * ^b -> ^c) x, y)
let inline minimum (x : ^a) (y : ^b) : ^c = ((^a or ^b) : (static member Min : ^a * ^b -> ^c) x, y)

//type System.Single with
//    static member LogSumExp(x:float32) = x
//    static member SoftPlus(x) = log (1.f + exp x)
//    static member SoftSign(x) = x / (1.f + abs x)
//    static member Sigmoid(x) = 1.f / (1.f + exp -x)
//    static member ReLU(x) = max 0.f x
//
//type System.Double with
//    static member LogSumExp(x:float) = x
//    static member SoftPlus(x) = log (1. + exp x)
//    static member SoftSign(x) = x / (1. + abs x)
//    static member Sigmoid(x) = 1. / (1. + exp -x)
//    static member ReLU(x) = max 0. x

module ErrorMessages = 
    let InvalidArgDiffn() = invalidArg "" "Order of differentiation cannot be negative."
    let InvalidArgSolve() = invalidArg "" "Given system of linear equations has no solution."
    let InvalidArgCurl() = invalidArg "" "Curl is supported only for functions with a three-by-three Jacobian matrix."
    let InvalidArgDiv() = invalidArg "" "Div is defined only for functions with a square Jacobian matrix."
    let InvalidArgCurlDiv() = 
        invalidArg "" "Curldiv is supported only for functions with a three-by-three Jacobian matrix."
    let InvalidArgInverse() = invalidArg "" "Cannot compute the inverse of given matrix."
    let InvalidArgDet() = invalidArg "" "Cannot compute the determinant of given matrix."
    let InvalidArgVV() = invalidArg "" "Vectors must have same length."
    let InvalidArgMColsMRows() = 
        invalidArg "" "Number of colums of first matrix must match number of rows of second matrix."
    let InvalidArgMM() = invalidArg "" "Matrices must have same shape."
    let InvalidArgVMRows() = invalidArg "" "Length of vector must match number of rows of matrix."
    let InvalidArgVMCols() = invalidArg "" "Length of vector must match number of columns of matrix."

type ISigmaDiffDataBuffer<'T> = 
    abstract Length : int32
    abstract Offset : int32
    abstract Data : 'T[]
    abstract SubData : 'T[]
    abstract GetValues : int32 -> int32 -> ISigmaDiffDataBuffer<'T>
    abstract GetStackedValues : int32 -> int32 -> int32 -> int32 -> int32 -> int32 -> ISigmaDiffDataBuffer<'T> 
    abstract DeepCopy : unit -> ISigmaDiffDataBuffer<'T>
    abstract ShallowCopy : unit -> ISigmaDiffDataBuffer<'T>

type DataBufferSubDataUtils =
    static member SubData<'T> (data : 'T[]) (offset : int32) (length : int32) =
        data.[offset..(offset + length - 1)]

type NativeDataBuffer<'T>(data : 'T [], offset : int32, length : int32) = 

    let mutable _length = length
    let mutable _offset = offset
    let mutable _data = data
    new(data : 'T []) = NativeDataBuffer<'T>(data, 0, data.Length)

    interface ISigmaDiffDataBuffer<'T> with 
        override d.Length = _length
        override d.Offset = _offset
        override d.Data = _data
        override d.SubData =  _data.[_offset..(_offset + _length - 1)]
        override d.GetValues startIndex length = NativeDataBuffer<'T>(_data, _offset + offset, length) :> ISigmaDiffDataBuffer<'T>
        override d.GetStackedValues rows cols rowStart rowFinish colStart colFinish = failwithf "Call to not implemented GetStackedValues function in NativeDataBuffer."
        override d.ShallowCopy() = NativeDataBuffer<'T>(data, offset, length) :> ISigmaDiffDataBuffer<'T>
        override d.DeepCopy() = NativeDataBuffer<'T>((Array.copy data), offset, length) :> ISigmaDiffDataBuffer<'T>
        end

     override d.ToString() = sprintf "DataBuffer-%i %A" _length (d :> ISigmaDiffDataBuffer<'T>).SubData

type ShapedDataBufferView<'T>(buffer : ISigmaDiffDataBuffer<'T>, [<ParamArray>] shape : int64 []) = 
    let checkshape (s : int64[]) = 
        if (s.Length <= 1) then
            failwithf "Internal error: Cannot create shaped data buffer view without columns dimension (rank <= 1, _shape: %A)" s
        s
    let _buffer = buffer
    let mutable _shape = (checkshape(shape))
//    do printfn "construct with shape %A\n from %A" shape System.Environment.StackTrace
    member d.DataBuffer = _buffer
    member d.Rows = int32 _shape.[0]
    member d.Cols = 
        if (_shape.Length <= 1) then
            failwithf "Internal error: Requested columns of shaped data buffer view without columns dimension (_shape: %A)" _shape
        int32 _shape.[1]
    member d.Length = _buffer.Length
        
    member d.Shape
        with get() = _shape
        and set (v : int64[]) = 
            if (v.Length <= 1) then
                failwithf "Internal error: Cannot set shaped data buffer view shape without columns dimension (rank <= 1, _shape: %A)" v
//            do printfn "set with shape %A" v
            _shape <- v

    member d.Item 
        with get (i : int32, j : int32) = _buffer.Data.[_buffer.Offset + (i * d.Rows + j)]
        and set (i : int32, j : int32) value = _buffer.Data.[_buffer.Offset + (i * d.Rows + j)] <- value
    
    member d.FlatItem 
        with get (i : int32) = _buffer.Data.[_buffer.Offset + i]

    member d.GetSlice(row, colStart, colFinish) =
        let colStart = defaultArg colStart 0
        let colFinish = defaultArg colFinish (d.Cols - 1)

        ShapedDataBufferView((_buffer.GetValues (row * d.Cols) (colFinish - colStart + 1)), int64 1, int64 (colFinish - colStart + 1))

    member d.GetSlice(rowStart, rowFinish, colStart, colFinish) =
        let rowStart = defaultArg rowStart 0
        let rowFinish = defaultArg rowFinish (d.Rows - 1)
        let colStart = defaultArg colStart 0
        let colFinish = defaultArg colFinish (d.Cols - 1)

        ShapedDataBufferView((_buffer.GetStackedValues d.Rows d.Cols rowStart rowFinish colStart colFinish), int64 (rowFinish - rowStart + 1), int64 (colFinish - colStart + 1))

    member d.ShallowCopy() = ShapedDataBufferView(_buffer.ShallowCopy(), (Array.copy _shape))
    member d.DeepCopy() = ShapedDataBufferView(_buffer.DeepCopy(), (Array.copy _shape))

    override d.ToString() = sprintf "ShapedDataBuffer view %O as %A" buffer _shape 

/// Tagger for generating incremental integers
type Tagger = 
    val mutable LastTag : uint32
    new(t) = { LastTag = t }
    member t.Next() = 
        t.LastTag <- t.LastTag + 1u
        t.LastTag

/// Global tagger for nested D operations
type GlobalTagger() = 
    static let T = new Tagger(0u)
    static member Next = T.Next()
    static member Reset = T.LastTag <- 0u

/// Extensions for the FSharp.Collections.Array module
module Array = 
    module Parallel = 
        let map2 f (a1 : _ []) (a2 : _ []) = 
            let n = min a1.Length a2.Length
            Array.Parallel.init n (fun i -> f a1.[i] a2.[i])
