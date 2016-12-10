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
namespace DiffSharp.Interop.Float64

open DiffSharp.Util
open System
open DiffSharp.Backend

type number = float
type IDataBuffer = IDataBuffer<number>
type internal ADD = DiffSharp.AD.Float64.DNumber

and DNumber(x:ADD) =
    new(x:float) = DNumber(ADD.D(x))
    member internal this.toADD() = x
    static member internal ADDtoD (x:ADD) = new DNumber(x)
    static member internal DtoADD (x:DNumber) = x.toADD()

    member d.P = d.toADD().P |> DNumber.ADDtoD
    member d.T = d.toADD().T |> DNumber.ADDtoD
    member d.A = d.toADD().A |> DNumber.ADDtoD

    override d.ToString() =
        let rec s (d:ADD) =
            match d with
            | DiffSharp.AD.Float64.D(p) -> sprintf "D %A" p
            | DiffSharp.AD.Float64.DF(p,t,_) -> sprintf "DF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float64.DR(p,a,_,_,_) -> sprintf "DR (%A, %A)"  (s p) (s !a)
        s (d.toADD())
    static member op_Implicit(d:DNumber):float = float (d.toADD())
    static member op_Implicit(a:float):DNumber = DNumber(a)
    static member Zero = DNumber(0.)
    static member One = DNumber(1.)
    interface System.IComparable with
        override d.CompareTo(other) =
            match other with
            | :? DNumber as d2 -> compare (d.toADD()) (d2.toADD())
            | _ -> invalidArg "" "Cannot compare this D with another type of object."
    override d.Equals(other) =
        match other with
        | :? DNumber as d2 -> compare (d.toADD()) (d2.toADD()) = 0
        | _ -> false
    override d.GetHashCode() = d.toADD().GetHashCode()
    // D - D binary operations
    static member (+) (a:DNumber, b:DNumber) = DNumber(a.toADD() + b.toADD())
    static member (-) (a:DNumber, b:DNumber) = DNumber(a.toADD() - b.toADD())
    static member (*) (a:DNumber, b:DNumber) = DNumber(a.toADD() * b.toADD())
    static member (/) (a:DNumber, b:DNumber) = DNumber(a.toADD() / b.toADD())
    static member Pow (a:DNumber, b:DNumber) = DNumber(a.toADD() ** b.toADD())
    static member Atan2 (a:DNumber, b:DNumber) = DNumber(atan2 (a.toADD()) (b.toADD()))
    // D - float binary operations
    static member (+) (a:DNumber, b:float) = a + (DNumber b)
    static member (-) (a:DNumber, b:float) = a - (DNumber b)
    static member (*) (a:DNumber, b:float) = a * (DNumber b)
    static member (/) (a:DNumber, b:float) = a / (DNumber b)
    static member Pow (a:DNumber, b:float) = a ** (DNumber b)
    static member Atan2 (a:DNumber, b:float) = atan2 a (DNumber b)
    // float - D binary operations
    static member (+) (a:float, b:DNumber) = (DNumber a) + b
    static member (-) (a:float, b:DNumber) = (DNumber a) - b
    static member (*) (a:float, b:DNumber) = (DNumber a) * b
    static member (/) (a:float, b:DNumber) = (DNumber a) / b
    static member Pow (a:float, b:DNumber) = (DNumber a) ** b
    static member Atan2 (a:float, b:DNumber) = atan2 (DNumber a) b
    // D - int binary operations
    static member (+) (a:DNumber, b:int) = a + (DNumber (float b))
    static member (-) (a:DNumber, b:int) = a - (DNumber (float b))
    static member (*) (a:DNumber, b:int) = a * (DNumber (float b))
    static member (/) (a:DNumber, b:int) = a / (DNumber (float b))
    static member Pow (a:DNumber, b:int) = DNumber.Pow(a, (DNumber (float b)))
    static member Atan2 (a:DNumber, b:int) = DNumber.Atan2(a, (DNumber (float b)))
    // int - D binary operations
    static member (+) (a:int, b:DNumber) = (DNumber (float a)) + b
    static member (-) (a:int, b:DNumber) = (DNumber (float a)) - b
    static member (*) (a:int, b:DNumber) = (DNumber (float a)) * b
    static member (/) (a:int, b:DNumber) = (DNumber (float a)) / b
    static member Pow (a:int, b:DNumber) = DNumber.Pow((DNumber (float a)), b)
    static member Atan2 (a:int, b:DNumber) = DNumber.Atan2((DNumber (float a)), b)
    // D unary operations
    static member Log (a:DNumber) = DNumber(log (a.toADD()))
    static member Log10 (a:DNumber) = DNumber(log10 (a.toADD()))
    static member Exp (a:DNumber) = DNumber(exp (a.toADD()))
    static member Sin (a:DNumber) = DNumber(sin (a.toADD()))
    static member Cos (a:DNumber) = DNumber(cos (a.toADD()))
    static member Tan (a:DNumber) = DNumber(tan (a.toADD()))
    static member Neg (a:DNumber) = DNumber(-(a.toADD()))
    static member Sqrt (a:DNumber) = DNumber(sqrt (a.toADD()))
    static member Sinh (a:DNumber) = DNumber(sinh (a.toADD()))
    static member Cosh (a:DNumber) = DNumber(cosh (a.toADD()))
    static member Tanh (a:DNumber) = DNumber(tanh (a.toADD()))
    static member Asin (a:DNumber) = DNumber(asin (a.toADD()))
    static member Acos (a:DNumber) = DNumber(acos (a.toADD()))
    static member Atan (a:DNumber) = DNumber(atan (a.toADD()))
    static member Abs (a:DNumber) = DNumber(abs (a.toADD()))
    static member Floor (a:DNumber) = DNumber(floor (a.toADD()))
    static member Ceiling (a:DNumber) = DNumber(ceil (a.toADD()))
    static member Round (a:DNumber) = DNumber(round (a.toADD()))
    static member Sign (a:DNumber) = DNumber(ADD.Sign(a.toADD()))
    static member SoftPlus (a:DNumber) = DNumber(ADD.SoftPlus(a.toADD()))
    static member SoftSign (a:DNumber) = DNumber(ADD.SoftSign(a.toADD()))
    static member Max (a:DNumber, b:DNumber) = DNumber(ADD.Max(a.toADD(), b.toADD()))
    static member Min (a:DNumber, b:DNumber) = DNumber(ADD.Min(a.toADD(), b.toADD()))

and internal ADDV = DiffSharp.AD.Float64.DVector

and DVector(v:ADDV) =
    new(v:IDataBuffer) = DVector(ADDV.DV(v))
    new(v:DNumber[]) = DVector(DiffSharp.AD.Float64.DOps.toDV(v |> Array.map DNumber.DtoADD))
    member internal this.toADDV() = v
    static member internal ADDVtoDV (v:ADDV) = new DVector(v)
    static member internal DVtoADDV (v:DVector) = v.toADDV()

    member d.P = d.toADDV().P |> DVector.ADDVtoDV
    member d.T = d.toADDV().T |> DVector.ADDVtoDV
    member d.A = d.toADDV().A |> DVector.ADDVtoDV

    member d.Item
        with get i = d.toADDV().[i] |> DNumber.ADDtoD

    override d.ToString() =
        let rec s (d:ADDV) =
            match d with
            | DiffSharp.AD.Float64.DV(p) -> sprintf "DV %A" p
            | DiffSharp.AD.Float64.DVF(p,t,_) -> sprintf "DVF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float64.DVR(p,a,_,_,_) -> sprintf "DVR (%A, %A)" (s p) (s !a)
        s (d.toADDV())
    member d.Visualize() = d.toADDV().Visualize()
    static member op_Implicit(d:DVector):IDataBuffer = d.toADDV().Buffer
    static member op_Implicit(a:IDataBuffer):DVector = DVector(a)
    static member Zero = DVector(DataBuffer<number>(Array.empty<float>))
    // DV - DV binary operations
    static member (+) (a:DVector, b:DVector) = DVector(a.toADDV() + b.toADDV())
    static member (-) (a:DVector, b:DVector) = DVector(a.toADDV() - b.toADDV())
    static member (*) (a:DVector, b:DVector) = DNumber(a.toADDV() * b.toADDV())
    static member (.*) (a:DVector, b:DVector) = DVector(a.toADDV() .* b.toADDV())
    static member (&*) (a:DVector, b:DVector) = DNDArray(a.toADDV() &* b.toADDV())
    static member (./) (a:DVector, b:DVector) = DVector(a.toADDV() ./ b.toADDV())
    static member Pow (a:DVector, b:DVector) = DVector(a.toADDV() ** b.toADDV())
    static member Atan2 (a:DVector, b:DVector) = DVector(atan2 (a.toADDV()) (b.toADDV()))
    // DV - D binary operations
    static member (+) (a:DVector, b:DNumber) = DVector(a.toADDV() + b.toADD())
    static member (-) (a:DVector, b:DNumber) = DVector(a.toADDV() - b.toADD())
    static member (*) (a:DVector, b:DNumber) = DVector(a.toADDV() * b.toADD())
    static member (/) (a:DVector, b:DNumber) = DVector(a.toADDV() / b.toADD())
    static member Pow (a:DVector, b:DNumber) = DVector(a.toADDV() ** b.toADD())
    static member Atan2 (a:DVector, b:DNumber) = DVector(ADDV.Atan2(a.toADDV(), b.toADD()))
    // D - DV binary operations
    static member (+) (a:DNumber, b:DVector) = DVector(a.toADD() + b.toADDV())
    static member (-) (a:DNumber, b:DVector) = DVector(a.toADD() - b.toADDV())
    static member (*) (a:DNumber, b:DVector) = DVector(a.toADD() * b.toADDV())
    static member (/) (a:DNumber, b:DVector) = DVector(a.toADD() / b.toADDV())
    static member Pow (a:DNumber, b:DVector) = DVector(ADDV.Pow(a.toADD(), b.toADDV()))
    static member Atan2 (a:DNumber, b:DVector) = DVector(ADDV.Atan2(a.toADD(), b.toADDV()))
    // DV - float binary operations
    static member (+) (a:DVector, b:float) = a + (DNumber b)
    static member (-) (a:DVector, b:float) = a - (DNumber b)
    static member (*) (a:DVector, b:float) = a * (DNumber b)
    static member (/) (a:DVector, b:float) = a / (DNumber b)
    static member Pow (a:DVector, b:float) = a ** (DNumber b)
    static member Atan2 (a:DVector, b:float) = DVector.Atan2(a, DNumber b)
    // float - DV binary operations
    static member (+) (a:float, b:DVector) = (DNumber a) + b
    static member (-) (a:float, b:DVector) = (DNumber a) - b
    static member (*) (a:float, b:DVector) = (DNumber a) * b
    static member (/) (a:float, b:DVector) = (DNumber a) / b
    static member Pow (a:float, b:DVector) = DVector.Pow(DNumber a, b)
    static member Atan2 (a:float, b:DVector) = DVector.Atan2(DNumber a, b)
    // DV - int binary operations
    static member (+) (a:DVector, b:int) = a + (DNumber (float b))
    static member (-) (a:DVector, b:int) = a - (DNumber (float b))
    static member (*) (a:DVector, b:int) = a * (DNumber (float b))
    static member (/) (a:DVector, b:int) = a / (DNumber (float b))
    static member Pow (a:DVector, b:int) = DVector.Pow(a, (DNumber (float b)))
    static member Atan2 (a:DVector, b:int) = DVector.Atan2(a, (DNumber (float b)))
    // int - DV binary operations
    static member (+) (a:int, b:DVector) = (DNumber (float a)) + b
    static member (-) (a:int, b:DVector) = (DNumber (float a)) - b
    static member (*) (a:int, b:DVector) = (DNumber (float a)) * b
    static member (/) (a:int, b:DVector) = (DNumber (float a)) / b
    static member Pow (a:int, b:DVector) = DVector.Pow((DNumber (float a)), b)
    static member Atan2 (a:int, b:DVector) = DVector.Atan2((DNumber (float a)), b)
    // DV unary operations
    static member Log (a:DVector) = DVector(log (a.toADDV()))
    static member Log10 (a:DVector) = DVector(log10 (a.toADDV()))
    static member Exp (a:DVector) = DVector(exp (a.toADDV()))
    static member Sin (a:DVector) = DVector(sin (a.toADDV()))
    static member Cos (a:DVector) = DVector(cos (a.toADDV()))
    static member Tan (a:DVector) = DVector(tan (a.toADDV()))
    static member Neg (a:DVector) = DVector(-(a.toADDV()))
    static member Sqrt (a:DVector) = DVector(sqrt (a.toADDV()))
    static member Sinh (a:DVector) = DVector(sinh (a.toADDV()))
    static member Cosh (a:DVector) = DVector(cosh (a.toADDV()))
    static member Tanh (a:DVector) = DVector(tanh (a.toADDV()))
    static member Asin (a:DVector) = DVector(asin (a.toADDV()))
    static member Acos (a:DVector) = DVector(acos (a.toADDV()))
    static member Atan (a:DVector) = DVector(atan (a.toADDV()))
    static member Abs (a:DVector) = DVector(abs (a.toADDV()))
    static member Floor (a:DVector) = DVector(floor (a.toADDV()))
    static member Ceiling (a:DVector) = DVector(ceil (a.toADDV()))
    static member Round (a:DVector) = DVector(round (a.toADDV()))
    static member Sign (a:DVector) = DVector(ADDV.Sign(a.toADDV()))
    static member SoftPlus (a:DVector) = DVector(ADDV.SoftPlus(a.toADDV()))
    static member SoftSign (a:DVector) = DVector(ADDV.SoftSign(a.toADDV()))
    static member Max (a:DVector, b:DVector) = DVector(ADDV.Max(a.toADDV(), b.toADDV()))
    static member Min (a:DVector, b:DVector) = DVector(ADDV.Min(a.toADDV(), b.toADDV()))
    static member Sum (a:DVector) = DNumber(ADDV.Sum(a.toADDV()))
    static member L1Norm (a:DVector) = DNumber(ADDV.L1Norm(a.toADDV()))
    static member L2Norm (a:DVector) = DNumber(ADDV.L2Norm(a.toADDV()))
    static member L2NormSq (a:DVector) = DNumber(ADDV.L2NormSq(a.toADDV()))
    static member Max (a:DVector) = DNumber(ADDV.Max(a.toADDV()))
    static member MaxIndex (a:DVector) = ADDV.MaxIndex(a.toADDV())
    static member Min (a:DVector) = DNumber(ADDV.Min(a.toADDV()))
    static member MinIndex (a:DVector) = ADDV.MinIndex(a.toADDV())
    static member SoftMax (a:DVector) = DVector(ADDV.SoftMax(a.toADDV()))
    static member Mean (a:DVector) = DNumber(ADDV.Mean(a.toADDV()))
    static member StandardDev (a:DVector) = DNumber(ADDV.StandardDev(a.toADDV()))
    static member Variance (a:DVector) = DNumber(ADDV.Variance(a.toADDV()))
    static member Normalize (a:DVector) = DVector(ADDV.Normalize(a.toADDV()))
    static member Standardize (a:DVector) = DVector(ADDV.Standardize(a.toADDV()))

and ADDND = DiffSharp.AD.Float64.DNDArray

and DNDArray(m:ADDND) =
    new(data:IDataBuffer<number>, [<ParamArray>] shape : int64[]) = DNDArray(ADDND.DM(ShapedDataBufferView<number>(data, shape)))
    member internal this.toADDM() = m
    static member internal ADDMtoDM (x:ADDND) = new DNDArray(x)
    static member internal DMtoADDM (x:DNDArray) = x.toADDM()

    member d.P = d.toADDM().P |> DNDArray.ADDMtoDM
    member d.T = d.toADDM().T |> DNDArray.ADDMtoDM
    member d.A = d.toADDM().A |> DNDArray.ADDMtoDM

    override d.ToString() =
        let rec s (d:ADDND) =
            match d with
            | DiffSharp.AD.Float64.DM(p) -> sprintf "DM %A" p
            | DiffSharp.AD.Float64.DMF(p,t,_) -> sprintf "DMF (%A, %A)" (s p) (s t)
            | DiffSharp.AD.Float64.DMR(p,a,_,_,_) -> sprintf "DMR (%A, %A)" (s p) (s !a)
        s (d.toADDM())
    member d.Visualize() = d.toADDM().Visualize()
    static member Zero = ADDND.Zero

    // DV - DV binary operations
    static member (+) (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() + b.toADDM())
    static member (-) (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() - b.toADDM())
    static member (*) (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() * b.toADDM())
    static member (.*) (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() .* b.toADDM())
    static member (./) (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() ./ b.toADDM())
    static member Pow (a:DNDArray, b:DNDArray) = DNDArray(a.toADDM() ** b.toADDM())
    static member Atan2 (a:DNDArray, b:DNDArray) = DNDArray(atan2 (a.toADDM()) (b.toADDM()))
    // DV - D binary operations
    static member (+) (a:DNDArray, b:DNumber) = DNDArray(a.toADDM() + b.toADD())
    static member (-) (a:DNDArray, b:DNumber) = DNDArray(a.toADDM() - b.toADD())
    static member (*) (a:DNDArray, b:DNumber) = DNDArray(a.toADDM() * b.toADD())
    static member (/) (a:DNDArray, b:DNumber) = DNDArray(a.toADDM() / b.toADD())
    static member Pow (a:DNDArray, b:DNumber) = DNDArray(a.toADDM() ** b.toADD())
    static member Atan2 (a:DNDArray, b:DNumber) = DNDArray(ADDND.Atan2(a.toADDM(), b.toADD()))
    // D - DV binary operations
    static member (+) (a:DNumber, b:DNDArray) = DNDArray(a.toADD() + b.toADDM())
    static member (-) (a:DNumber, b:DNDArray) = DNDArray(a.toADD() - b.toADDM())
    static member (*) (a:DNumber, b:DNDArray) = DNDArray(a.toADD() * b.toADDM())
    static member (/) (a:DNumber, b:DNDArray) = DNDArray(a.toADD() / b.toADDM())
    static member Pow (a:DNumber, b:DNDArray) = DNDArray(ADDND.Pow(a.toADD(), b.toADDM()))
    static member Atan2 (a:DNumber, b:DNDArray) = DNDArray(ADDND.Atan2(a.toADD(), b.toADDM()))
    // DV - float binary operations
    static member (+) (a:DNDArray, b:float) = a + (DNumber b)
    static member (-) (a:DNDArray, b:float) = a - (DNumber b)
    static member (*) (a:DNDArray, b:float) = a * (DNumber b)
    static member (/) (a:DNDArray, b:float) = a / (DNumber b)
    static member Pow (a:DNDArray, b:float) = a ** (DNumber b)
    static member Atan2 (a:DNDArray, b:float) = DNDArray.Atan2(a, DNumber b)
    // float - DV binary operations
    static member (+) (a:float, b:DNDArray) = (DNumber a) + b
    static member (-) (a:float, b:DNDArray) = (DNumber a) - b
    static member (*) (a:float, b:DNDArray) = (DNumber a) * b
    static member (/) (a:float, b:DNDArray) = (DNumber a) / b
    static member Pow (a:float, b:DNDArray) = DNDArray.Pow(DNumber a, b)
    static member Atan2 (a:float, b:DNDArray) = DNDArray.Atan2(DNumber a, b)
    // DV - int binary operations
    static member (+) (a:DNDArray, b:int) = a + (DNumber (float b))
    static member (-) (a:DNDArray, b:int) = a - (DNumber (float b))
    static member (*) (a:DNDArray, b:int) = a * (DNumber (float b))
    static member (/) (a:DNDArray, b:int) = a / (DNumber (float b))
    static member Pow (a:DNDArray, b:int) = DNDArray.Pow(a, (DNumber (float b)))
    static member Atan2 (a:DNDArray, b:int) = DNDArray.Atan2(a, (DNumber (float b)))
    // int - DV binary operations
    static member (+) (a:int, b:DNDArray) = (DNumber (float a)) + b
    static member (-) (a:int, b:DNDArray) = (DNumber (float a)) - b
    static member (*) (a:int, b:DNDArray) = (DNumber (float a)) * b
    static member (/) (a:int, b:DNDArray) = (DNumber (float a)) / b
    static member Pow (a:int, b:DNDArray) = DNDArray.Pow((DNumber (float a)), b)
    static member Atan2 (a:int, b:DNDArray) = DNDArray.Atan2((DNumber (float a)), b)
    // DV unary operations
    static member Log (a:DNDArray) = DNDArray(log (a.toADDM()))
    static member Log10 (a:DNDArray) = DNDArray(log10 (a.toADDM()))
    static member Exp (a:DNDArray) = DNDArray(exp (a.toADDM()))
    static member Sin (a:DNDArray) = DNDArray(sin (a.toADDM()))
    static member Cos (a:DNDArray) = DNDArray(cos (a.toADDM()))
    static member Tan (a:DNDArray) = DNDArray(tan (a.toADDM()))
    static member Neg (a:DNDArray) = DNDArray(-(a.toADDM()))
    static member Sqrt (a:DNDArray) = DNDArray(sqrt (a.toADDM()))
    static member Sinh (a:DNDArray) = DNDArray(sinh (a.toADDM()))
    static member Cosh (a:DNDArray) = DNDArray(cosh (a.toADDM()))
    static member Tanh (a:DNDArray) = DNDArray(tanh (a.toADDM()))
    static member Asin (a:DNDArray) = DNDArray(asin (a.toADDM()))
    static member Acos (a:DNDArray) = DNDArray(acos (a.toADDM()))
    static member Atan (a:DNDArray) = DNDArray(atan (a.toADDM()))
    static member Abs (a:DNDArray) = DNDArray(abs (a.toADDM()))
    static member Floor (a:DNDArray) = DNDArray(floor (a.toADDM()))
    static member Ceiling (a:DNDArray) = DNDArray(ceil (a.toADDM()))
    static member Round (a:DNDArray) = DNDArray(round (a.toADDM()))
    static member Sign (a:DNDArray) = DNDArray(ADDND.Sign(a.toADDM()))
    static member Sum (a:DNDArray) = DNumber(ADDND.Sum(a.toADDM()))
    static member Transpose (a:DNDArray) = DNDArray(ADDND.Transpose(a.toADDM()))
    static member Diagonal (a:DNDArray) = DVector(ADDND.Diagonal(a.toADDM()))
    static member Trace (a:DNDArray) = DNumber(ADDND.Trace(a.toADDM()))
    static member Solve (a:DNDArray, b:DVector) = DVector(ADDND.Solve(a.toADDM(), b.toADDV()))
    static member SolveSymmetric (a:DNDArray, b:DVector) = DVector(ADDND.SolveSymmetric(a.toADDM(), b.toADDV()))
    static member Inverse (a:DNDArray) = DNDArray(ADDND.Inverse(a.toADDM()))
    static member Det (a:DNDArray) = DNumber(ADDND.Det(a.toADDM()))
    static member ReLU (a:DNDArray) = DNDArray(ADDND.ReLU(a.toADDM()))
    static member Sigmoid (a:DNDArray) = DNDArray(ADDND.Sigmoid(a.toADDM()))
    static member SoftPlus (a:DNDArray) = DNDArray(ADDND.SoftPlus(a.toADDM()))
    static member SoftSign (a:DNDArray) = DNDArray(ADDND.SoftSign(a.toADDM()))
    static member Max (a:DNDArray, b:DNDArray) = DNDArray(ADDND.Max(a.toADDM(), b.toADDM()))
    static member Min (a:DNDArray, b:DNDArray) = DNDArray(ADDND.Min(a.toADDM(), b.toADDM()))
    static member Max (a:DNDArray, b:DNumber) = DNDArray(ADDND.Max(a.toADDM(), b.toADD()))
    static member Max (a:DNumber, b:DNDArray) = DNDArray(ADDND.Max(a.toADD(), b.toADDM()))
    static member Min (a:DNDArray, b:DNumber) = DNDArray(ADDND.Min(a.toADDM(), b.toADD()))
    static member Min (a:DNumber, b:DNDArray) = DNDArray(ADDND.Min(a.toADD(), b.toADDM()))
    static member MaxIndex (a:DNDArray) = ADDND.MaxIndex(a.toADDM())
    static member MinIndex (a:DNDArray) = ADDND.MinIndex(a.toADDM())
    static member Mean (a:DNDArray) = DNumber(ADDND.Mean(a.toADDM()))
    static member StandardDev (a:DNDArray) = DNumber(ADDND.StandardDev(a.toADDM()))
    static member Variance (a:DNDArray) = DNumber(ADDND.Variance(a.toADDM()))
    static member Normalize (a:DNDArray) = DNDArray(ADDND.Normalize(a.toADDM()))
    static member Standardize (a:DNDArray) = DNDArray(ADDND.Standardize(a.toADDM()))

/// Nested forward and reverse mode automatic differentiation module
type AD =
    /// First derivative of a scalar-to-scalar function `f`
    static member Diff(f:System.Func<DNumber,DNumber>) = System.Func<DNumber,DNumber>(DNumber.DtoADD >> (DiffSharp.AD.Float64.DiffOps.diff (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD)) >> DNumber.ADDtoD)
    /// First derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diff(f:System.Func<DNumber,DNumber>, x:DNumber) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.diff (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    /// Second derivative of a scalar-to-scalar function `f`
    static member Diff2(f:System.Func<DNumber,DNumber>) = System.Func<DNumber,DNumber>(DNumber.DtoADD >> (DiffSharp.AD.Float64.DiffOps.diff2 (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD)) >> DNumber.ADDtoD)
    /// Second derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diff2(f:System.Func<DNumber,DNumber>, x:DNumber) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.diff2 (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    /// `n`-th derivative of a scalar-to-scalar function `f`
    static member Diffn(n:int, f:System.Func<DNumber,DNumber>) = System.Func<DNumber,DNumber>(DNumber.DtoADD >> (DiffSharp.AD.Float64.DiffOps.diffn n (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD)) >> DNumber.ADDtoD)
    /// `n`-th derivative of a scalar-to-scalar function `f`, at point `x`
    static member Diffn(n:int, f:System.Func<DNumber,DNumber>, x:DNumber) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.diffn n (DNumber.ADDtoD >> f.Invoke >> DNumber.DtoADD) (x |> DNumber.DtoADD)
    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
    static member Gradv(f:System.Func<DVector,DNumber>, x:DVector, v:DVector) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.gradv (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    /// Gradient of a vector-to-scalar function `f`
    static member Grad(f:System.Func<DVector,DNumber>) = System.Func<DVector,DVector>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.grad (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD)) >> DVector.ADDVtoDV)
    /// Gradient of a vector-to-scalar function `f`, at point `x`
    static member Grad(f:System.Func<DVector,DNumber>, x:DVector) = DVector.ADDVtoDV <| DiffSharp.AD.Float64.DiffOps.grad ((DVector.ADDVtoDV) >> f.Invoke >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    /// Laplacian of a vector-to-scalar function `f`
    static member Laplacian(f:System.Func<DVector,DNumber>) = System.Func<DVector,DNumber>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.laplacian (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD)) >> DNumber.ADDtoD)
    /// Laplacian of a vector-to-scalar function `f`, at point `x`
    static member Laplacian(f:System.Func<DVector,DNumber>, x:DVector) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.laplacian (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    static member Jacobianv(f:System.Func<DVector,DVector>, x:DVector, v:DVector) = DVector.ADDVtoDV <| DiffSharp.AD.Float64.DiffOps.jacobianv (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    /// Transposed Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    static member JacobianTv(f:System.Func<DVector,DVector>, x:DVector, v:DVector) = DVector.ADDVtoDV <| DiffSharp.AD.Float64.DiffOps.jacobianTv (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    /// Jacobian of a vector-to-vector function `f`
    static member Jacobian(f:System.Func<DVector,DVector>) = System.Func<DVector,DNDArray>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.jacobian (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV)) >> DNDArray.ADDMtoDM)
    /// Jacobian of a vector-to-vector function `f`, at point `x`
    static member Jacobian(f:System.Func<DVector,DVector>, x:DVector) = DNDArray.ADDMtoDM <| DiffSharp.AD.Float64.DiffOps.jacobian (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    /// Transposed Jacobian of a vector-to-vector function `f`
    static member JacobianT(f:System.Func<DVector,DVector>) = System.Func<DVector,DNDArray>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.jacobianT (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV)) >> DNDArray.ADDMtoDM)
    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`
    static member JacobianT(f:System.Func<DVector,DVector>, x:DVector) = DNDArray.ADDMtoDM <| DiffSharp.AD.Float64.DiffOps.jacobianT (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    /// Hessian of a vector-to-scalar function `f`
    static member Hessian(f:System.Func<DVector,DNumber>) = System.Func<DVector,DNDArray>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.hessian (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD)) >> DNDArray.ADDMtoDM)
    /// Hessian of a vector-to-scalar function `f`, at point `x`
    static member Hessian(f:System.Func<DVector,DNumber>, x:DVector) = DNDArray.ADDMtoDM <| DiffSharp.AD.Float64.DiffOps.hessian (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD) (x |> DVector.DVtoADDV)
    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`
    static member Hessianv(f:System.Func<DVector,DNumber>, x:DVector, v:DVector) = DVector.ADDVtoDV <| DiffSharp.AD.Float64.DiffOps.hessianv (DVector.ADDVtoDV >> f.Invoke >> DNumber.DtoADD) (x |> DVector.DVtoADDV) (v |> DVector.DVtoADDV)
    /// Curl of a vector-to-vector function `f`. Supported only for functions with a three-by-three Jacobian matrix.
    static member Curl(f:System.Func<DVector,DVector>) = System.Func<DVector,DVector>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.curl (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV)) >> DVector.ADDVtoDV)
    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    static member Curl(f:System.Func<DVector,DVector>, x:DVector) = DVector.ADDVtoDV <| DiffSharp.AD.Float64.DiffOps.curl (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    /// Divergence of a vector-to-vector function `f`. Defined only for functions with a square Jacobian matrix.
    static member Div(f:System.Func<DVector,DVector>) = System.Func<DVector,DNumber>(DVector.DVtoADDV >> (DiffSharp.AD.Float64.DiffOps.div (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV)) >> DNumber.ADDtoD)
    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
    static member Div(f:System.Func<DVector,DVector>, x:DVector) = DNumber.ADDtoD <| DiffSharp.AD.Float64.DiffOps.div (DVector.ADDVtoDV >> f.Invoke >> DVector.DVtoADDV) (x |> DVector.DVtoADDV)
    /// Returns a specified number raised to the specified power.
    static member inline Pow(a:'T, b:'U) = a ** b
    /// Returns the angle whose tangent is the quotient of two specified numbers.
    static member inline Atan2(a:'T, b:'T) = atan2 a b
    /// Returns the logarithm of a specified number.
    static member inline Log(a:'T) = log a
    /// Returns the base 10 logarithm of a specified number.
    static member inline Log10(a:'T) = log10 a
    /// Returns e raised to the specified power.
    static member inline Exp(a:'T) = exp a
    /// Returns the sine of the specified angle.
    static member inline Sin(a:'T) = sin a
    /// Returns the cosine of the specified angle.
    static member inline Cos(a:'T) = cos a
    /// Returns the tangent of the specified angle.
    static member inline Tan(a:'T) = tan a
    /// Returns the square root of a specified number.
    static member inline Sqrt(a:'T) = sqrt a
    /// Returns the hyperbolic sine of the specified angle.
    static member inline Sinh(a:'T) = sinh a
    /// Returns the hyperbolic cosine of the specified angle.
    static member inline Cosh(a:'T) = cosh a
    /// Returns the hyperbolic tangent of the specified angle.
    static member inline Tanh(a:'T) = tanh a
    /// Returns the angle whose sine is the specified number.
    static member inline Asin(a:'T) = asin a
    /// Returns the angle whose cosine is the specified number.
    static member inline Acos(a:'T) = acos a
    /// Returns the angle whose tangent is the specified number.
    static member inline Atan(a:'T) = atan a
    /// Returns the absolute value of a specified number.
    static member inline Abs(a:'T) = abs a
    /// Returns the largest integer less than or equal to the specified number.
    static member inline Floor(a:'T) = floor a
    /// Returns the smallest integer greater than or equal to the specified number.
    static member inline Ceiling(a:'T) = ceil a
    /// Rounds a value to the nearest integer or to the specified number of fractional digits.
    static member inline Round(a:'T) = round a
    /// Returns the larger of two specified numbers.
    /// Returns the smaller of two numbers.
    static member inline Min(a:'T, b:'T) = min a b
    static member inline LogSumExp(a:'T) = (^T : (static member LogSumExp : ^T -> ^U) a)
    static member inline SoftPlus(a:'T) = (^T : (static member SoftPlus : ^T -> ^T) a)
    static member inline SoftSign(a:'T) = (^T : (static member SoftSign : ^T -> ^T) a)
    static member inline Sigmoid(a:'T) = (^T : (static member Sigmoid : ^T -> ^T) a)
    static member inline ReLU(a:'T) = (^T : (static member ReLU : ^T -> ^T) a)
    static member inline SoftMax(a:'T) = (^T : (static member SoftMax : ^T -> ^T) a)
    static member inline Max(a:'T, b:'U):^V = ((^T or ^U) : (static member Max : ^T * ^U -> ^V) a, b)
    static member inline Min(a:'T, b:'U):^V = ((^T or ^U) : (static member Min : ^T * ^U -> ^V) a, b)
    static member inline Signum(a:'T) = (^T : (static member Sign : ^T -> ^T) a)
    static member inline Mean(a:'T) = (^T : (static member Mean : ^T -> DNumber) a)
    static member inline StandardDev(a:'T) = (^T : (static member StandardDev : ^T -> DNumber) a)
    static member inline Variance(a:'T) = (^T : (static member Variance : ^T -> DNumber) a)
    static member inline Normalize(a:'T) = (^T : (static member Normalize : ^T -> ^T) a)
    static member inline Standardize(a:'T) = (^T : (static member Standardize : ^T -> ^T) a)
    static member L1Norm(a:DVector) = DNumber(ADDV.L1Norm(a.toADDV()))
    static member L2Norm(a:DVector) = DNumber(ADDV.L2Norm(a.toADDV()))
    static member L2NormSq(a:DVector) = DNumber(ADDV.L2NormSq(a.toADDV()))
    static member Sum(a:DVector) = DNumber(ADDV.Sum(a.toADDV()))
    static member Sum(a:DNDArray) = DNumber(ADDND.Sum(a.toADDM()))
    static member Transpose (a:DNDArray) = DNDArray(ADDND.Transpose(a.toADDM()))
    static member Diagonal (a:DNDArray) = DVector(ADDND.Diagonal(a.toADDM()))
    static member Trace (a:DNDArray) = DNumber(ADDND.Trace(a.toADDM()))
    static member Solve (a:DNDArray, b:DVector) = DVector(ADDND.Solve(a.toADDM(), b.toADDV()))
    static member SolveSymmetric (a:DNDArray, b:DVector) = DVector(ADDND.SolveSymmetric(a.toADDM(), b.toADDV()))
    static member Inverse (a:DNDArray) = DNDArray(ADDND.Inverse(a.toADDM()))


/// Numerical differentiation module
//type Numerical =
//    /// First derivative of a scalar-to-scalar function `f`
//    static member Diff(f:System.Func<float,float>, backend:Backend<number>) = System.Func<float, float, Backend<number>>(DiffSharp.Numerical.Float64.DiffOps.diff f.Invoke backend)
//    /// First derivative of a scalar-to-scalar function `f`, at point `x`
//    static member Diff(f:System.Func<float,float>, x:float, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.diff f.Invoke x
//    /// Second derivative of a scalar-to-scalar function `f`
//    static member Diff2(f:System.Func<float,float>, backend:Backend<number>) = System.Func<float, float>(DiffSharp.Numerical.Float64.DiffOps.diff2 f.Invoke backend)
//    /// Second derivative of a scalar-to-scalar function `f`, at point `x`
//    static member Diff2(f:System.Func<float,float>, x:float, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.diff2 f.Invoke x
//    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
//    static member Gradv(f:System.Func<IDataBuffer,float>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.gradv f.Invoke x v
//    /// Gradient of a vector-to-scalar function `f`
//    static member Grad(f:System.Func<IDataBuffer,float>, backend:Backend<number>) = System.Func<IDataBuffer,IDataBuffer>(DiffSharp.Numerical.Float64.DiffOps.grad f.Invoke)
//    /// Gradient of a vector-to-scalar function `f`, at point `x`
//    static member Grad(f:System.Func<IDataBuffer,float>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.grad f.Invoke x
//    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`
//    static member Hessianv(f:System.Func<IDataBuffer,float>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.hessianv f.Invoke x v
//    /// Hessian of a vector-to-scalar function `f`
//    static member Hessian(f:System.Func<IDataBuffer,float>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float64.DiffOps.hessian f.Invoke)
//    /// Hessian of a vector-to-scalar function `f`, at point `x`
//    static member Hessian(f:System.Func<IDataBuffer,float>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.hessian f.Invoke x
//    /// Laplacian of a vector-to-scalar function `f`
//    static member Laplacian(f:System.Func<IDataBuffer,float>, backend:Backend<number>) = System.Func<IDataBuffer,float>(DiffSharp.Numerical.Float64.DiffOps.laplacian f.Invoke)
//    /// Laplacian of a vector-to-scalar function `f`, at point `x`
//    static member Laplacian(f:System.Func<IDataBuffer,float>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.laplacian f.Invoke x
//    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
//    static member Jacobianv(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, v:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.jacobianv f.Invoke x v
//    /// Jacobian of a vector-to-vector function `f`
//    static member Jacobian(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float64.DiffOps.jacobian f.Invoke)
//    /// Jacobian of a vector-to-vector function `f`, at point `x`
//    static member Jacobian(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.jacobian f.Invoke x
//    /// Transposed Jacobian of a vector-to-vector function `f`
//    static member JacobianT(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,ShapedDataBufferView<number>>(DiffSharp.Numerical.Float64.DiffOps.jacobianT f.Invoke)
//    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`
//    static member JacobianT(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.jacobianT f.Invoke x
////    /// Curl of a vector-to-vector function `f`. Supported only for functions with a three-by-three Jacobian matrix.
////    static member Curl(f:System.Func<IDataBuffer,IDataBuffer>) = System.Func<IDataBuffer,IDataBuffer>(DiffSharp.Numerical.Float64.DiffOps.curl f.Invoke)
//    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
//    static member Curl(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.curl f.Invoke x
//    /// Divergence of a vector-to-vector function `f`. Defined only for functions with a square Jacobian matrix.
//    static member Div(f:System.Func<IDataBuffer,IDataBuffer>, backend:Backend<number>) = System.Func<IDataBuffer,float>(DiffSharp.Numerical.Float64.DiffOps.div f.Invoke)
//    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
//    static member Div(f:System.Func<IDataBuffer,IDataBuffer>, x:IDataBuffer, backend:Backend<number>) = DiffSharp.Numerical.Float64.DiffOps.div f.Invoke x backend

