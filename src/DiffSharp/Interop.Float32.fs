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
/// Interoperability layer, for C# and other CLR languages
namespace DiffSharp.Interop.Float32

open DiffSharp.Util
open System

type number = float32

type IDataBuffer = ISigmaDiffDataBuffer<number>

type internal ADD = DiffSharp.AD.Float32.DNumber

and DNumber(x : ADD) = 
    new(x : float32) = DNumber(ADD.D(x))
    member internal this.asADD = x
    static member internal ADDtoD(x : ADD) = new DNumber(x)
    static member internal DtoADD(x : DNumber) = x.asADD 
    member d.P = d.asADD.P |> DNumber.ADDtoD
    member d.T = d.asADD.T |> DNumber.ADDtoD
    member d.A = d.asADD.A |> DNumber.ADDtoD
    member d.Value = d.asADD.Value 
    member d.GetReverse(i : uint32) = d.asADD.GetReverse(i) |> DNumber.ADDtoD

    override d.ToString() = 
        let rec s (d : ADD) = 
            match d with
            | DiffSharp.AD.Float32.D(p) -> sprintf "D %A" p
            | DiffSharp.AD.Float32.DF(p, t, _) -> sprintf "DF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float32.DR(p, a, _, _, _) -> sprintf "DR (%A, %A)" (s p) (s !a)
        s (d.asADD)
    
    static member op_Implicit (d : DNumber) : float32 = float32 (d.asADD)
    static member op_Implicit (a : float32) : DNumber = DNumber(a)
    static member Zero = DNumber(0.f)
    static member One = DNumber(1.f)
    
    interface System.IComparable with
        member d.CompareTo(other) = 
            match other with
            | :? DNumber as d2 -> compare (d.asADD) (d2.asADD)
            | _ -> invalidArg "" "Cannot compare this D with another type of object."
    
    override d.Equals(other) = 
        match other with
        | :? DNumber as d2 -> compare (d.asADD) (d2.asADD) = 0
        | _ -> false
    
    override d.GetHashCode() = d.asADD.GetHashCode()
    // D - D binary operations
    static member (+) (a : DNumber, b : DNumber) = DNumber(a.asADD + b.asADD)
    static member (-) (a : DNumber, b : DNumber) = DNumber(a.asADD - b.asADD)
    static member (*) (a : DNumber, b : DNumber) = DNumber(a.asADD * b.asADD)
    static member (/) (a : DNumber, b : DNumber) = DNumber(a.asADD / b.asADD)
    static member Pow(a : DNumber, b : DNumber) = DNumber(a.asADD ** b.asADD)
    static member Atan2(a : DNumber, b : DNumber) = DNumber(atan2 (a.asADD) (b.asADD))
    // D - float32 binary operations
    static member (+) (a : DNumber, b : float32) = a + (DNumber b)
    static member (-) (a : DNumber, b : float32) = a - (DNumber b)
    static member (*) (a : DNumber, b : float32) = a * (DNumber b)
    static member (/) (a : DNumber, b : float32) = a / (DNumber b)
    static member Pow(a : DNumber, b : float32) = a ** (DNumber b)
    static member Atan2(a : DNumber, b : float32) = atan2 a (DNumber b)
    // float32 - D binary operations
    static member (+) (a : float32, b : DNumber) = (DNumber a) + b
    static member (-) (a : float32, b : DNumber) = (DNumber a) - b
    static member (*) (a : float32, b : DNumber) = (DNumber a) * b
    static member (/) (a : float32, b : DNumber) = (DNumber a) / b
    static member Pow(a : float32, b : DNumber) = (DNumber a) ** b
    static member Atan2(a : float32, b : DNumber) = atan2 (DNumber a) b
    // D - int binary operations
    static member (+) (a : DNumber, b : int) = a + (DNumber(float32 b))
    static member (-) (a : DNumber, b : int) = a - (DNumber(float32 b))
    static member (*) (a : DNumber, b : int) = a * (DNumber(float32 b))
    static member (/) (a : DNumber, b : int) = a / (DNumber(float32 b))
    static member Pow(a : DNumber, b : int) = DNumber.Pow(a, (DNumber(float32 b)))
    static member Atan2(a : DNumber, b : int) = DNumber.Atan2(a, (DNumber(float32 b)))
    // int - D binary operations
    static member (+) (a : int, b : DNumber) = (DNumber(float32 a)) + b
    static member (-) (a : int, b : DNumber) = (DNumber(float32 a)) - b
    static member (*) (a : int, b : DNumber) = (DNumber(float32 a)) * b
    static member (/) (a : int, b : DNumber) = (DNumber(float32 a)) / b
    static member Pow(a : int, b : DNumber) = DNumber.Pow((DNumber(float32 a)), b)
    static member Atan2(a : int, b : DNumber) = DNumber.Atan2((DNumber(float32 a)), b)
    // D unary operations
    static member Log(a : DNumber) = DNumber(log (a.asADD))
    static member Log10(a : DNumber) = DNumber(log10 (a.asADD))
    static member Exp(a : DNumber) = DNumber(exp (a.asADD))
    static member Sin(a : DNumber) = DNumber(sin (a.asADD))
    static member Cos(a : DNumber) = DNumber(cos (a.asADD))
    static member Tan(a : DNumber) = DNumber(tan (a.asADD))
    static member Neg(a : DNumber) = DNumber(-(a.asADD))
    static member Sqrt(a : DNumber) = DNumber(sqrt (a.asADD))
    static member Sinh(a : DNumber) = DNumber(sinh (a.asADD))
    static member Cosh(a : DNumber) = DNumber(cosh (a.asADD))
    static member Tanh(a : DNumber) = DNumber(tanh (a.asADD))
    static member Asin(a : DNumber) = DNumber(asin (a.asADD))
    static member Acos(a : DNumber) = DNumber(acos (a.asADD))
    static member Atan(a : DNumber) = DNumber(atan (a.asADD))
    static member Abs(a : DNumber) = DNumber(abs (a.asADD))
    static member Floor(a : DNumber) = DNumber(floor (a.asADD))
    static member Ceiling(a : DNumber) = DNumber(ceil (a.asADD))
    static member Round(a : DNumber) = DNumber(round (a.asADD))
    static member Sign(a : DNumber) = DNumber(ADD.Sign(a.asADD))
    static member SoftPlus(a : DNumber) = DNumber(ADD.SoftPlus(a.asADD))
    static member SoftSign(a : DNumber) = DNumber(ADD.SoftSign(a.asADD))
    static member Max(a : DNumber, b : DNumber) = DNumber(ADD.Max(a.asADD, b.asADD))
    static member Min(a : DNumber, b : DNumber) = DNumber(ADD.Min(a.asADD, b.asADD))

and internal ADDV = DiffSharp.AD.Float32.DVector

and DVector(v : ADDV) = 
    new(v : IDataBuffer) = DVector(ADDV.DV(v))
    new(v : DNumber []) = DVector(DiffSharp.AD.Float32.DOps.toDV (v |> Array.map DNumber.DtoADD))
    member internal this.asADDV = v
    static member internal ADDVtoDV(v : ADDV) = new DVector(v)
    static member internal DVtoADDV(v : DVector) = v.asADDV
    member d.P = d.asADDV.P |> DVector.ADDVtoDV
    member d.T = d.asADDV.T |> DVector.ADDVtoDV
    member d.A = d.asADDV.A |> DVector.ADDVtoDV
    member d.Buffer = d.asADDV.Buffer
    member d.Item 
        with get i = d.asADDV.[i] |> DNumber.ADDtoD
    member d.GetReverse(i : uint32) = d.asADDV.GetReverse(i) |> DVector.ADDVtoDV

    override d.ToString() = 
        let rec s (d : ADDV) = 
            match d with
            | DiffSharp.AD.Float32.DV(p) -> sprintf "DV %A" p
            | DiffSharp.AD.Float32.DVF(p, t, _) -> sprintf "DVF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float32.DVR(p, a, _, _, _) -> sprintf "DVR (%A, %A)" (s p) (s !a)
        s (d.asADDV)
    
    member d.Visualize() = d.asADDV.Visualize()
    static member op_Implicit (d : DVector) : IDataBuffer = d.asADDV.Buffer
    static member op_Implicit (a : IDataBuffer) : DVector = DVector(a)
    static member Zero = DVector(NativeDataBuffer<number>(Array.empty<float32>))
    // DV - DV binary operations
    static member (+) (a : DVector, b : DVector) = DVector(a.asADDV + b.asADDV)
    static member (-) (a : DVector, b : DVector) = DVector(a.asADDV - b.asADDV)
    static member (*) (a : DVector, b : DVector) = DNumber(a.asADDV * b.asADDV)
    static member (.*) (a : DVector, b : DVector) = DVector(a.asADDV .* b.asADDV)
    static member (&*) (a : DVector, b : DVector) = DNDArray(a.asADDV &* b.asADDV)
    static member (./) (a : DVector, b : DVector) = DVector(a.asADDV ./ b.asADDV)
    static member Pow(a : DVector, b : DVector) = DVector(a.asADDV ** b.asADDV)
    static member Atan2(a : DVector, b : DVector) = DVector(atan2 (a.asADDV) (b.asADDV))
    // DV - D binary operations
    static member (+) (a : DVector, b : DNumber) = DVector(a.asADDV + b.asADD)
    static member (-) (a : DVector, b : DNumber) = DVector(a.asADDV - b.asADD)
    static member (*) (a : DVector, b : DNumber) = DVector(a.asADDV * b.asADD)
    static member (/) (a : DVector, b : DNumber) = DVector(a.asADDV / b.asADD)
    static member Pow(a : DVector, b : DNumber) = DVector(a.asADDV ** b.asADD)
    static member Atan2(a : DVector, b : DNumber) = DVector(ADDV.Atan2(a.asADDV, b.asADD))
    // D - DV binary operations
    static member (+) (a : DNumber, b : DVector) = DVector(a.asADD + b.asADDV)
    static member (-) (a : DNumber, b : DVector) = DVector(a.asADD - b.asADDV)
    static member (*) (a : DNumber, b : DVector) = DVector(a.asADD * b.asADDV)
    static member (/) (a : DNumber, b : DVector) = DVector(a.asADD / b.asADDV)
    static member Pow(a : DNumber, b : DVector) = DVector(ADDV.Pow(a.asADD, b.asADDV))
    static member Atan2(a : DNumber, b : DVector) = DVector(ADDV.Atan2(a.asADD, b.asADDV))
    // DV - float32 binary operations
    static member (+) (a : DVector, b : float32) = a + (DNumber b)
    static member (-) (a : DVector, b : float32) = a - (DNumber b)
    static member (*) (a : DVector, b : float32) = a * (DNumber b)
    static member (/) (a : DVector, b : float32) = a / (DNumber b)
    static member Pow(a : DVector, b : float32) = a ** (DNumber b)
    static member Atan2(a : DVector, b : float32) = DVector.Atan2(a, DNumber b)
    // float32 - DV binary operations
    static member (+) (a : float32, b : DVector) = (DNumber a) + b
    static member (-) (a : float32, b : DVector) = (DNumber a) - b
    static member (*) (a : float32, b : DVector) = (DNumber a) * b
    static member (/) (a : float32, b : DVector) = (DNumber a) / b
    static member Pow(a : float32, b : DVector) = DVector.Pow(DNumber a, b)
    static member Atan2(a : float32, b : DVector) = DVector.Atan2(DNumber a, b)
    // DV - int binary operations
    static member (+) (a : DVector, b : int) = a + (DNumber(float32 b))
    static member (-) (a : DVector, b : int) = a - (DNumber(float32 b))
    static member (*) (a : DVector, b : int) = a * (DNumber(float32 b))
    static member (/) (a : DVector, b : int) = a / (DNumber(float32 b))
    static member Pow(a : DVector, b : int) = DVector.Pow(a, (DNumber(float32 b)))
    static member Atan2(a : DVector, b : int) = DVector.Atan2(a, (DNumber(float32 b)))
    // int - DV binary operations
    static member (+) (a : int, b : DVector) = (DNumber(float32 a)) + b
    static member (-) (a : int, b : DVector) = (DNumber(float32 a)) - b
    static member (*) (a : int, b : DVector) = (DNumber(float32 a)) * b
    static member (/) (a : int, b : DVector) = (DNumber(float32 a)) / b
    static member Pow(a : int, b : DVector) = DVector.Pow((DNumber(float32 a)), b)
    static member Atan2(a : int, b : DVector) = DVector.Atan2((DNumber(float32 a)), b)
    // DV unary operations
    static member Log(a : DVector) = DVector(log (a.asADDV))
    static member Log10(a : DVector) = DVector(log10 (a.asADDV))
    static member Exp(a : DVector) = DVector(exp (a.asADDV))
    static member Sin(a : DVector) = DVector(sin (a.asADDV))
    static member Cos(a : DVector) = DVector(cos (a.asADDV))
    static member Tan(a : DVector) = DVector(tan (a.asADDV))
    static member Neg(a : DVector) = DVector(-(a.asADDV))
    static member Sqrt(a : DVector) = DVector(sqrt (a.asADDV))
    static member Sinh(a : DVector) = DVector(sinh (a.asADDV))
    static member Cosh(a : DVector) = DVector(cosh (a.asADDV))
    static member Tanh(a : DVector) = DVector(tanh (a.asADDV))
    static member Asin(a : DVector) = DVector(asin (a.asADDV))
    static member Acos(a : DVector) = DVector(acos (a.asADDV))
    static member Atan(a : DVector) = DVector(atan (a.asADDV))
    static member Abs(a : DVector) = DVector(abs (a.asADDV))
    static member Floor(a : DVector) = DVector(floor (a.asADDV))
    static member Ceiling(a : DVector) = DVector(ceil (a.asADDV))
    static member Round(a : DVector) = DVector(round (a.asADDV))
    static member Sign(a : DVector) = DVector(ADDV.Sign(a.asADDV))
    static member SoftPlus(a : DVector) = DVector(ADDV.SoftPlus(a.asADDV))
    static member SoftSign(a : DVector) = DVector(ADDV.SoftSign(a.asADDV))
    static member Max(a : DVector, b : DVector) = DVector(ADDV.Max(a.asADDV, b.asADDV))
    static member Min(a : DVector, b : DVector) = DVector(ADDV.Min(a.asADDV, b.asADDV))
    static member Sum(a : DVector) = DNumber(ADDV.Sum(a.asADDV))
    static member L1Norm(a : DVector) = DNumber(ADDV.L1Norm(a.asADDV))
    static member L2Norm(a : DVector) = DNumber(ADDV.L2Norm(a.asADDV))
    static member L2NormSq(a : DVector) = DNumber(ADDV.L2NormSq(a.asADDV))
    static member Max(a : DVector) = DNumber(ADDV.Max(a.asADDV))
    static member MaxIndex(a : DVector) = ADDV.MaxIndex(a.asADDV)
    static member Min(a : DVector) = DNumber(ADDV.Min(a.asADDV))
    static member MinIndex(a : DVector) = ADDV.MinIndex(a.asADDV)
    static member SoftMax(a : DVector) = DVector(ADDV.SoftMax(a.asADDV))
    static member Mean(a : DVector) = DNumber(ADDV.Mean(a.asADDV))
    static member StandardDev(a : DVector) = DNumber(ADDV.StandardDev(a.asADDV))
    static member Variance(a : DVector) = DNumber(ADDV.Variance(a.asADDV))
    static member Normalize(a : DVector) = DVector(ADDV.Normalize(a.asADDV))
    static member Standardize(a : DVector) = DVector(ADDV.Standardize(a.asADDV))

and ADDND = DiffSharp.AD.Float32.DNDArray

and DNDArray(m : ADDND) = 
    new(data : ISigmaDiffDataBuffer<number>, [<ParamArray>] shape : int64 []) = 
        DNDArray(ADDND.DM(ShapedDataBufferView<number>(data, shape)))
    member internal this.asADDND = m
    static member internal ADDNDtoDND(x : ADDND) = new DNDArray(x)
    static member internal DMtoADDM(x : DNDArray) = x.asADDND      
    member d.P = d.asADDND.P |> DNDArray.ADDNDtoDND
    member d.T = d.asADDND.T |> DNDArray.ADDNDtoDND
    member d.A = d.asADDND.A |> DNDArray.ADDNDtoDND
    member d.Buffer = d.asADDND.Buffer
    member d.GetReverse(i : uint32) = d.asADDND.GetReverse(i) |> DNDArray.ADDNDtoDND

    override d.ToString() = 
        let rec s (d : ADDND) = 
            match d with
            | DiffSharp.AD.Float32.DM(p) -> sprintf "DM %A" p
            | DiffSharp.AD.Float32.DMF(p, t, _) -> sprintf "DMF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float32.DMR(p, a, _, _, _) -> sprintf "DMR (%A, %A)" (s p) (s !a)
        s (d.asADDND)
    
    member d.Visualize() = d.asADDND.Visualize()
    static member Zero = ADDND.Zero
    // DV - DV binary operations
    static member (+) (a : DNDArray, b : DNDArray) = DNDArray(a.asADDND + b.asADDND)
    static member (-) (a : DNDArray, b : DNDArray) = DNDArray(a.asADDND - b.asADDND)
    static member (*) (a : DNDArray, b : DNDArray) = DNDArray(a.asADDND * b.asADDND)
    static member (.*) (a : DNDArray, b : DNDArray) = DNDArray(a.asADDND .* b.asADDND)
    static member (./) (a : DNDArray, b : DNDArray) = DNDArray(a.asADDND ./ b.asADDND)
    static member Pow(a : DNDArray, b : DNDArray) = DNDArray(a.asADDND ** b.asADDND)
    static member Atan2(a : DNDArray, b : DNDArray) = DNDArray(atan2 (a.asADDND) (b.asADDND))
    // DV - D binary operations
    static member (+) (a : DNDArray, b : DNumber) = DNDArray(a.asADDND + b.asADD)
    static member (-) (a : DNDArray, b : DNumber) = DNDArray(a.asADDND - b.asADD)
    static member (*) (a : DNDArray, b : DNumber) = DNDArray(a.asADDND * b.asADD)
    static member (/) (a : DNDArray, b : DNumber) = DNDArray(a.asADDND / b.asADD)
    static member Pow(a : DNDArray, b : DNumber) = DNDArray(a.asADDND ** b.asADD)
    static member Atan2(a : DNDArray, b : DNumber) = DNDArray(ADDND.Atan2(a.asADDND, b.asADD))
    // D - DV binary operations
    static member (+) (a : DNumber, b : DNDArray) = DNDArray(a.asADD + b.asADDND)
    static member (-) (a : DNumber, b : DNDArray) = DNDArray(a.asADD - b.asADDND)
    static member (*) (a : DNumber, b : DNDArray) = DNDArray(a.asADD * b.asADDND)
    static member (/) (a : DNumber, b : DNDArray) = DNDArray(a.asADD / b.asADDND)
    static member Pow(a : DNumber, b : DNDArray) = DNDArray(ADDND.Pow(a.asADD, b.asADDND))
    static member Atan2(a : DNumber, b : DNDArray) = DNDArray(ADDND.Atan2(a.asADD, b.asADDND))
    // DV - float32 binary operations
    static member (+) (a : DNDArray, b : float32) = a + (DNumber b)
    static member (-) (a : DNDArray, b : float32) = a - (DNumber b)
    static member (*) (a : DNDArray, b : float32) = a * (DNumber b)
    static member (/) (a : DNDArray, b : float32) = a / (DNumber b)
    static member Pow(a : DNDArray, b : float32) = a ** (DNumber b)
    static member Atan2(a : DNDArray, b : float32) = DNDArray.Atan2(a, DNumber b)
    // float32 - DV binary operations
    static member (+) (a : float32, b : DNDArray) = (DNumber a) + b
    static member (-) (a : float32, b : DNDArray) = (DNumber a) - b
    static member (*) (a : float32, b : DNDArray) = (DNumber a) * b
    static member (/) (a : float32, b : DNDArray) = (DNumber a) / b
    static member Pow(a : float32, b : DNDArray) = DNDArray.Pow(DNumber a, b)
    static member Atan2(a : float32, b : DNDArray) = DNDArray.Atan2(DNumber a, b)
    // DV - int binary operations
    static member (+) (a : DNDArray, b : int) = a + (DNumber(float32 b))
    static member (-) (a : DNDArray, b : int) = a - (DNumber(float32 b))
    static member (*) (a : DNDArray, b : int) = a * (DNumber(float32 b))
    static member (/) (a : DNDArray, b : int) = a / (DNumber(float32 b))
    static member Pow(a : DNDArray, b : int) = DNDArray.Pow(a, (DNumber(float32 b)))
    static member Atan2(a : DNDArray, b : int) = DNDArray.Atan2(a, (DNumber(float32 b)))
    // int - DV binary operations
    static member (+) (a : int, b : DNDArray) = (DNumber(float32 a)) + b
    static member (-) (a : int, b : DNDArray) = (DNumber(float32 a)) - b
    static member (*) (a : int, b : DNDArray) = (DNumber(float32 a)) * b
    static member (/) (a : int, b : DNDArray) = (DNumber(float32 a)) / b
    static member Pow(a : int, b : DNDArray) = DNDArray.Pow((DNumber(float32 a)), b)
    static member Atan2(a : int, b : DNDArray) = DNDArray.Atan2((DNumber(float32 a)), b)
    // DV unary operations
    static member Log(a : DNDArray) = DNDArray(log (a.asADDND))
    static member Log10(a : DNDArray) = DNDArray(log10 (a.asADDND))
    static member Exp(a : DNDArray) = DNDArray(exp (a.asADDND))
    static member Sin(a : DNDArray) = DNDArray(sin (a.asADDND))
    static member Cos(a : DNDArray) = DNDArray(cos (a.asADDND))
    static member Tan(a : DNDArray) = DNDArray(tan (a.asADDND))
    static member Neg(a : DNDArray) = DNDArray(-(a.asADDND))
    static member Sqrt(a : DNDArray) = DNDArray(sqrt (a.asADDND))
    static member Sinh(a : DNDArray) = DNDArray(sinh (a.asADDND))
    static member Cosh(a : DNDArray) = DNDArray(cosh (a.asADDND))
    static member Tanh(a : DNDArray) = DNDArray(tanh (a.asADDND))
    static member Asin(a : DNDArray) = DNDArray(asin (a.asADDND))
    static member Acos(a : DNDArray) = DNDArray(acos (a.asADDND))
    static member Atan(a : DNDArray) = DNDArray(atan (a.asADDND))
    static member Abs(a : DNDArray) = DNDArray(abs (a.asADDND))
    static member Floor(a : DNDArray) = DNDArray(floor (a.asADDND))
    static member Ceiling(a : DNDArray) = DNDArray(ceil (a.asADDND))
    static member Round(a : DNDArray) = DNDArray(round (a.asADDND))
    static member Sign(a : DNDArray) = DNDArray(ADDND.Sign(a.asADDND))
    static member Sum(a : DNDArray) = DNumber(ADDND.Sum(a.asADDND))
    static member Transpose(a : DNDArray) = DNDArray(ADDND.Transpose(a.asADDND))
    static member Diagonal(a : DNDArray) = DVector(ADDND.Diagonal(a.asADDND))
    static member Trace(a : DNDArray) = DNumber(ADDND.Trace(a.asADDND))
    static member Solve(a : DNDArray, b : DVector) = DVector(ADDND.Solve(a.asADDND, b.asADDV))
    static member SolveSymmetric(a : DNDArray, b : DVector) = DVector(ADDND.SolveSymmetric(a.asADDND, b.asADDV))
    static member Inverse(a : DNDArray) = DNDArray(ADDND.Inverse(a.asADDND))
    static member Det(a : DNDArray) = DNumber(ADDND.Det(a.asADDND))
    static member ReLU(a : DNDArray) = DNDArray(ADDND.ReLU(a.asADDND))
    static member Sigmoid(a : DNDArray) = DNDArray(ADDND.Sigmoid(a.asADDND))
    static member SoftPlus(a : DNDArray) = DNDArray(ADDND.SoftPlus(a.asADDND))
    static member SoftSign(a : DNDArray) = DNDArray(ADDND.SoftSign(a.asADDND))
    static member Max(a : DNDArray, b : DNDArray) = DNDArray(ADDND.Max(a.asADDND, b.asADDND))
    static member Min(a : DNDArray, b : DNDArray) = DNDArray(ADDND.Min(a.asADDND, b.asADDND))
    static member Max(a : DNDArray, b : DNumber) = DNDArray(ADDND.Max(a.asADDND, b.asADD))
    static member Max(a : DNumber, b : DNDArray) = DNDArray(ADDND.Max(a.asADD, b.asADDND))
    static member Min(a : DNDArray, b : DNumber) = DNDArray(ADDND.Min(a.asADDND, b.asADD))
    static member Min(a : DNumber, b : DNDArray) = DNDArray(ADDND.Min(a.asADD, b.asADDND))
    static member MaxIndex(a : DNDArray) = ADDND.MaxIndex(a.asADDND)
    static member MinIndex(a : DNDArray) = ADDND.MinIndex(a.asADDND)
    static member Mean(a : DNDArray) = DNumber(ADDND.Mean(a.asADDND))
    static member StandardDev(a : DNDArray) = DNumber(ADDND.StandardDev(a.asADDND))
    static member Variance(a : DNDArray) = DNumber(ADDND.Variance(a.asADDND))
    static member Normalize(a : DNDArray) = DNDArray(ADDND.Normalize(a.asADDND))
    static member Standardize(a : DNDArray) = DNDArray(ADDND.Standardize(a.asADDND))

/// Nested forward and reverse mode automatic differentiation module
type AD = 
    
    /// First derivative of a scalar-to-scalar function `f`
    static member Diff(f : System.Func<DNumber, DNumber>) = 
        System.Func<DNumber, DNumber>(DNumber.DtoADD
                                      >> (DiffSharp.AD.Float32.DiffOps.diff (DNumber.ADDtoD
                                                                             >> f.Invoke
                                                                             >> DNumber.DtoADD))
                                      >> DNumber.ADDtoD)
    
    /// First derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diff(f : System.Func<DNumber, DNumber>, x : DNumber) = 
        DNumber.ADDtoD <| DiffSharp.AD.Float32.DiffOps.diff (DNumber.ADDtoD
                                                             >> f.Invoke
                                                             >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    
    /// Second derivative of a scalar-to-scalar function `f`
    static member Diff2(f : System.Func<DNumber, DNumber>) = 
        System.Func<DNumber, DNumber>(DNumber.DtoADD
                                      >> (DiffSharp.AD.Float32.DiffOps.diff2 (DNumber.ADDtoD
                                                                              >> f.Invoke
                                                                              >> DNumber.DtoADD))
                                      >> DNumber.ADDtoD)
    
    /// Second derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diff2(f : System.Func<DNumber, DNumber>, x : DNumber) = 
        DNumber.ADDtoD <| DiffSharp.AD.Float32.DiffOps.diff2 (DNumber.ADDtoD
                                                              >> f.Invoke
                                                              >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    
    /// `n`-th derivative of a scalar-to-scalar function `f`
    static member Diffn(n : int, f : System.Func<DNumber, DNumber>) = 
        System.Func<DNumber, DNumber>(DNumber.DtoADD
                                      >> (DiffSharp.AD.Float32.DiffOps.diffn n (DNumber.ADDtoD
                                                                                >> f.Invoke
                                                                                >> DNumber.DtoADD))
                                      >> DNumber.ADDtoD)
    
    /// `n`-th derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diffn(n : int, f : System.Func<DNumber, DNumber>, x : DNumber) = 
        DNumber.ADDtoD <| DiffSharp.AD.Float32.DiffOps.diffn n (DNumber.ADDtoD
                                                                >> f.Invoke
                                                                >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    
    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
    static member Gradv(f : System.Func<DVector, DNumber>, x : DVector, v : DVector) = 
        DNumber.ADDtoD 
        <| DiffSharp.AD.Float32.DiffOps.gradv (DVector.ADDVtoDV
                                               >> f.Invoke
                                               >> DNumber.DtoADD) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    
    /// Gradient of a vector-to-scalar function `f`
    static member Grad(f : System.Func<DVector, DNumber>) = 
        System.Func<DVector, DVector>(DVector.DVtoADDV
                                      >> (DiffSharp.AD.Float32.DiffOps.grad (DVector.ADDVtoDV
                                                                             >> f.Invoke
                                                                             >> DNumber.DtoADD))
                                      >> DVector.ADDVtoDV)
    
    /// Gradient of a vector-to-scalar function `f`, at point `x`
    static member Grad(f : System.Func<DVector, DNumber>, x : DVector) = 
        DVector.ADDVtoDV <| DiffSharp.AD.Float32.DiffOps.grad ((DVector.ADDVtoDV)
                                                               >> f.Invoke
                                                               >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    
    /// Laplacian of a vector-to-scalar function `f`
    static member Laplacian(f : System.Func<DVector, DNumber>) = 
        System.Func<DVector, DNumber>(DVector.DVtoADDV
                                      >> (DiffSharp.AD.Float32.DiffOps.laplacian (DVector.ADDVtoDV
                                                                                  >> f.Invoke
                                                                                  >> DNumber.DtoADD))
                                      >> DNumber.ADDtoD)
    
    /// Laplacian of a vector-to-scalar function `f`, at point `x`
    static member Laplacian(f : System.Func<DVector, DNumber>, x : DVector) = 
        DNumber.ADDtoD <| DiffSharp.AD.Float32.DiffOps.laplacian (DVector.ADDVtoDV
                                                                  >> f.Invoke
                                                                  >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    
    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    static member Jacobianv(f : System.Func<DVector, DVector>, x : DVector, v : DVector) = 
        DVector.ADDVtoDV 
        <| DiffSharp.AD.Float32.DiffOps.jacobianv (DVector.ADDVtoDV
                                                   >> f.Invoke
                                                   >> DVector.DVtoADDV) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    
    /// Transposed Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    static member JacobianTv(f : System.Func<DVector, DVector>, x : DVector, v : DVector) = 
        DVector.ADDVtoDV 
        <| DiffSharp.AD.Float32.DiffOps.jacobianTv (DVector.ADDVtoDV
                                                    >> f.Invoke
                                                    >> DVector.DVtoADDV) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    
    /// Jacobian of a vector-to-vector function `f`
    static member Jacobian(f : System.Func<DVector, DVector>) = 
        System.Func<DVector, DNDArray>(DVector.DVtoADDV
                                       >> (DiffSharp.AD.Float32.DiffOps.jacobian (DVector.ADDVtoDV
                                                                                  >> f.Invoke
                                                                                  >> DVector.DVtoADDV))
                                       >> DNDArray.ADDNDtoDND)
    
    /// Jacobian of a vector-to-vector function `f`, at point `x`
    static member Jacobian(f : System.Func<DVector, DVector>, x : DVector) = 
        DNDArray.ADDNDtoDND <| DiffSharp.AD.Float32.DiffOps.jacobian (DVector.ADDVtoDV
                                                                    >> f.Invoke
                                                                    >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    
    /// Transposed Jacobian of a vector-to-vector function `f`
    static member JacobianT(f : System.Func<DVector, DVector>) = 
        System.Func<DVector, DNDArray>(DVector.DVtoADDV
                                       >> (DiffSharp.AD.Float32.DiffOps.jacobianT (DVector.ADDVtoDV
                                                                                   >> f.Invoke
                                                                                   >> DVector.DVtoADDV))
                                       >> DNDArray.ADDNDtoDND)
    
    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`
    static member JacobianT(f : System.Func<DVector, DVector>, x : DVector) = 
        DNDArray.ADDNDtoDND <| DiffSharp.AD.Float32.DiffOps.jacobianT (DVector.ADDVtoDV
                                                                     >> f.Invoke
                                                                     >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    
    /// Hessian of a vector-to-scalar function `f`
    static member Hessian(f : System.Func<DVector, DNumber>) = 
        System.Func<DVector, DNDArray>(DVector.DVtoADDV
                                       >> (DiffSharp.AD.Float32.DiffOps.hessian (DVector.ADDVtoDV
                                                                                 >> f.Invoke
                                                                                 >> DNumber.DtoADD))
                                       >> DNDArray.ADDNDtoDND)
    
    /// Hessian of a vector-to-scalar function `f`, at point `x`
    static member Hessian(f : System.Func<DVector, DNumber>, x : DVector) = 
        DNDArray.ADDNDtoDND <| DiffSharp.AD.Float32.DiffOps.hessian (DVector.ADDVtoDV
                                                                   >> f.Invoke
                                                                   >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    
    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`
    static member Hessianv(f : System.Func<DVector, DNumber>, x : DVector, v : DVector) = 
        DVector.ADDVtoDV 
        <| DiffSharp.AD.Float32.DiffOps.hessianv (DVector.ADDVtoDV
                                                  >> f.Invoke
                                                  >> DNumber.DtoADD) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    
    /// Curl of a vector-to-vector function `f`. Supported only for functions with a three-by-three Jacobian matrix.
    static member Curl(f : System.Func<DVector, DVector>) = 
        System.Func<DVector, DVector>(DVector.DVtoADDV
                                      >> (DiffSharp.AD.Float32.DiffOps.curl (DVector.ADDVtoDV
                                                                             >> f.Invoke
                                                                             >> DVector.DVtoADDV))
                                      >> DVector.ADDVtoDV)
    
    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    static member Curl(f : System.Func<DVector, DVector>, x : DVector) = 
        DVector.ADDVtoDV <| DiffSharp.AD.Float32.DiffOps.curl (DVector.ADDVtoDV
                                                               >> f.Invoke
                                                               >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    
    /// Divergence of a vector-to-vector function `f`. Defined only for functions with a square Jacobian matrix.
    static member Div(f : System.Func<DVector, DVector>) = 
        System.Func<DVector, DNumber>(DVector.DVtoADDV
                                      >> (DiffSharp.AD.Float32.DiffOps.div (DVector.ADDVtoDV
                                                                            >> f.Invoke
                                                                            >> DVector.DVtoADDV))
                                      >> DNumber.ADDtoD)
    
    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
    static member Div(f : System.Func<DVector, DVector>, x : DVector) = 
        DNumber.ADDtoD <| DiffSharp.AD.Float32.DiffOps.div (DVector.ADDVtoDV
                                                            >> f.Invoke
                                                            >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    
    /// Returns a specified number raised to the specified power.
    static member inline Pow(a : 'T, b : 'U) = a ** b
    
    /// Returns the angle whose tangent is the quotient of two specified numbers.
    static member inline Atan2(a : 'T, b : 'T) = atan2 a b
    
    /// Returns the logarithm of a specified number.
    static member inline Log(a : 'T) = log a
    
    /// Returns the base 10 logarithm of a specified number.
    static member inline Log10(a : 'T) = log10 a
    
    /// Returns e raised to the specified power.
    static member inline Exp(a : 'T) = exp a
    
    /// Returns the sine of the specified angle.
    static member inline Sin(a : 'T) = sin a
    
    /// Returns the cosine of the specified angle.
    static member inline Cos(a : 'T) = cos a
    
    /// Returns the tangent of the specified angle.
    static member inline Tan(a : 'T) = tan a
    
    /// Returns the square root of a specified number.
    static member inline Sqrt(a : 'T) = sqrt a
    
    /// Returns the hyperbolic sine of the specified angle.
    static member inline Sinh(a : 'T) = sinh a
    
    /// Returns the hyperbolic cosine of the specified angle.
    static member inline Cosh(a : 'T) = cosh a
    
    /// Returns the hyperbolic tangent of the specified angle.
    static member inline Tanh(a : 'T) = tanh a
    
    /// Returns the angle whose sine is the specified number.
    static member inline Asin(a : 'T) = asin a
    
    /// Returns the angle whose cosine is the specified number.
    static member inline Acos(a : 'T) = acos a
    
    /// Returns the angle whose tangent is the specified number.
    static member inline Atan(a : 'T) = atan a
    
    /// Returns the absolute value of a specified number.
    static member inline Abs(a : 'T) = abs a
    
    /// Returns the largest integer less than or equal to the specified number.
    static member inline Floor(a : 'T) = floor a
    
    /// Returns the smallest integer greater than or equal to the specified number.
    static member inline Ceiling(a : 'T) = ceil a
    
    /// Rounds a value to the nearest integer or to the specified number of fractional digits.
    static member inline Round(a : 'T) = round a
    
    /// Returns the larger of two specified numbers.
    /// Returns the smaller of two numbers.
    static member inline Min(a : 'T, b : 'T) = min a b
    
    static member inline LogSumExp(a : 'T) = (^T : (static member LogSumExp : ^T -> ^U) a)
    static member inline SoftPlus(a : 'T) = (^T : (static member SoftPlus : ^T -> ^T) a)
    static member inline SoftSign(a : 'T) = (^T : (static member SoftSign : ^T -> ^T) a)
    static member inline Sigmoid(a : 'T) = (^T : (static member Sigmoid : ^T -> ^T) a)
    static member inline ReLU(a : 'T) = (^T : (static member ReLU : ^T -> ^T) a)
    static member inline SoftMax(a : 'T) = (^T : (static member SoftMax : ^T -> ^T) a)
    static member inline Max(a : 'T, b : 'U) : ^V = ((^T or ^U) : (static member Max : ^T * ^U -> ^V) a, b)
    static member inline Min(a : 'T, b : 'U) : ^V = ((^T or ^U) : (static member Min : ^T * ^U -> ^V) a, b)
    static member inline Signum(a : 'T) = (^T : (static member Sign : ^T -> ^T) a)
    static member inline Mean(a : 'T) = (^T : (static member Mean : ^T -> DNumber) a)
    static member inline StandardDev(a : 'T) = (^T : (static member StandardDev : ^T -> DNumber) a)
    static member inline Variance(a : 'T) = (^T : (static member Variance : ^T -> DNumber) a)
    static member inline Normalize(a : 'T) = (^T : (static member Normalize : ^T -> ^T) a)
    static member inline Standardize(a : 'T) = (^T : (static member Standardize : ^T -> ^T) a)
    static member L1Norm(a : DVector) = DNumber(ADDV.L1Norm(a.asADDV))
    static member L2Norm(a : DVector) = DNumber(ADDV.L2Norm(a.asADDV))
    static member L2NormSq(a : DVector) = DNumber(ADDV.L2NormSq(a.asADDV))
    static member Sum(a : DVector) = DNumber(ADDV.Sum(a.asADDV))
    static member Sum(a : DNDArray) = DNumber(ADDND.Sum(a.asADDND))
    static member Transpose(a : DNDArray) = DNDArray(ADDND.Transpose(a.asADDND))
    static member Diagonal(a : DNDArray) = DVector(ADDND.Diagonal(a.asADDND))
    static member Trace(a : DNDArray) = DNumber(ADDND.Trace(a.asADDND))
    static member Solve(a : DNDArray, b : DVector) = DVector(ADDND.Solve(a.asADDND, b.asADDV))
    static member SolveSymmetric(a : DNDArray, b : DVector) = DVector(ADDND.SolveSymmetric(a.asADDND, b.asADDV))
    static member Inverse(a : DNDArray) = DNDArray(ADDND.Inverse(a.asADDND))
/// Numerical differentiation module
//type Numerical =
//    /// First derivative of a scalar-to-scalar function `f`
//    static member Diff(f:System.Func<float32,float32>, backend:Backend<number>) = System.Func<float32, float32, Backend<number>>(DiffSharp.Numerical.Float32.DiffOps.diff f.Invoke backend)
//    /// First derivative of a scalar-to-scalar function `f`, at point `x`
//    static member Diff(f:System.Func<float32,float32>, x:float32, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.diff f.Invoke x
//    /// Second derivative of a scalar-to-scalar function `f`
//    static member Diff2(f:System.Func<float32,float32>, backend:Backend<number>) = System.Func<float32, float32>(DiffSharp.Numerical.Float32.DiffOps.diff2 f.Invoke backend)
//    /// Second derivative of a scalar-to-scalar function `f`, at point `x`
//    static member Diff2(f:System.Func<float32,float32>, x:float32, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.diff2 f.Invoke x
//    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
//    static member Gradv(f:System.Func<IDataBuffer,float32>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.gradv f.Invoke x v
//    /// Gradient of a vector-to-scalar function `f`
//    static member Grad(f:System.Func<IDataBuffer,float32>, backend:Backend<number>) = System.Func<IDataBuffer,IDataBuffer>(DiffSharp.Numerical.Float32.DiffOps.grad f.Invoke)
//    /// Gradient of a vector-to-scalar function `f`, at point `x`
//    static member Grad(f:System.Func<IDataBuffer,float32>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.grad f.Invoke x
//    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`
//    static member Hessianv(f:System.Func<IDataBuffer,float32>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.hessianv f.Invoke x v
//    /// Hessian of a vector-to-scalar function `f`
//    static member Hessian(f:System.Func<IDataBuffer,float32>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float32.DiffOps.hessian f.Invoke)
//    /// Hessian of a vector-to-scalar function `f`, at point `x`
//    static member Hessian(f:System.Func<IDataBuffer,float32>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.hessian f.Invoke x
//    /// Laplacian of a vector-to-scalar function `f`
//    static member Laplacian(f:System.Func<IDataBuffer,float32>, backend:Backend<number>) = System.Func<IDataBuffer,float32>(DiffSharp.Numerical.Float32.DiffOps.laplacian f.Invoke)
//    /// Laplacian of a vector-to-scalar function `f`, at point `x`
//    static member Laplacian(f:System.Func<IDataBuffer,float32>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.laplacian f.Invoke x
//    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
//    static member Jacobianv(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.jacobianv f.Invoke x v
//    /// Jacobian of a vector-to-vector function `f`
//    static member Jacobian(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float32.DiffOps.jacobian f.Invoke)
//    /// Jacobian of a vector-to-vector function `f`, at point `x`
//    static member Jacobian(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.jacobian f.Invoke x
//    /// Transposed Jacobian of a vector-to-vector function `f`
//    static member JacobianT(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float32.DiffOps.jacobianT f.Invoke)
//    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`
//    static member JacobianT(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.jacobianT f.Invoke x
////    /// Curl of a vector-to-vector function `f`. Supported only for functions with a three-by-three Jacobian matrix.
////    static member Curl(f:System.Func<IDataBuffer,IDataBuffer>) = System.Func<IDataBuffer,IDataBuffer>(DiffSharp.Numerical.Float32.DiffOps.curl f.Invoke)
//    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
//    static member Curl(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.curl f.Invoke x
//    /// Divergence of a vector-to-vector function `f`. Defined only for functions with a square Jacobian matrix.
//    static member Div(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,float32>(DiffSharp.Numerical.Float32.DiffOps.div f.Invoke)
//    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
//    static member Div(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float32.DiffOps.div f.Invoke x backend
