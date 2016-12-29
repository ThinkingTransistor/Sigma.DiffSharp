using System;
using DiffSharp;
using DiffSharp.AD;
using static DiffSharp.Interop.Float64.AD;
using DiffSharp.Interop.Float64;

namespace InteropTest
{
	public static class Program
	{
		// Define a function whose derivative you need
		// F(x) = Sin(x^2 - Exp(x))
		public static DNumber F(DNumber x)
		{
			return Sin(x * x - Exp(x));
		}

		public static void Main(string[] args)
		{
			DNumber a = new DNumber(1.0f).GetReverse(0);

			DNumber b = a * 2;
			DNDArray array = new DNDArray(new Util.NativeDataBuffer<double>(new double[] {1, 2, 3, 4, 5, 6}), new long[] { 2, 3 });

			DNumber c = AD.Sum(array * b);

			Float64.DOps.reverseProp(new DNumber(1.0f).asADD, c.asADD);

			Console.WriteLine(b.A.Value);

			Console.ReadKey();
		}
	}

	public class NDArray : DNDArray
	{
		public NDArray(Float64.DNDArray m) : base(m)
		{
		}
	}
}
