import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{Tools from BKLNW}
In this file we record the results from
S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, Sharper bounds for the Chebyshev function θ(x),
Math. Comp. 90 (2021), no. 331, 2281–2315.
--/

open Real

noncomputable def BKLNW.f (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 3 ⌊ (log x)/(log 2) ⌋, x^(1/k - 1/3)

noncomputable def BKLNW.ε (b : ℝ) : ℝ :=
  if b < 20 then 0   -- junk value
  else if b < 21 then 4.2670e-5
  else if b < 22 then 2.58843e-5
  else if b < 23 then 1.56996e-5
  else if b < 24 then 9.52229e-6
  else if b < 25 then 5.77556e-6
  else if b < 30 then 3.50306e-6
  else if b < 35 then 2.87549e-7
  else if b < 40 then 2.36034e-8
  else if b < 45 then 1.93378e-8
  else if b < 50 then 1.09073e-8
  else if b < 100 then 1.11990e-9
  else if b < 200 then 2.45299e-12
  else if b < 300 then 2.18154e-12
  else if b < 400 then 2.09022e-12
  else if b < 500 then 2.03981e-12
  else if b < 600 then 1.99986e-12
  else if b < 700 then 1.98894e-12
  else if b < 800 then 1.97643e-12
  else if b < 900 then 1.96710e-12
  else if b < 1000 then 1.95987e-12
  else if b < 1500 then 1.94751e-12
  else if b < 2000 then 1.93677e-12
  else if b < 2500 then 1.92279e-12
  else if b < 3000 then 9.06304e-13
  else if b < 3500 then 4.59972e-14
  else if b < 4000 then 2.48641e-15
  else if b < 4500 then 1.42633e-16
  else if b < 5000 then 8.68295e-18
  else if b < 5500 then 5.63030e-19
  else if b < 6000 then 3.91348e-20
  else if b < 6500 then 2.94288e-21
  else if b < 7000 then 2.38493e-22
  else if b < 7500 then 2.07655e-23
  else if b < 8000 then 1.96150e-24
  else if b < 8500 then 1.97611e-25
  else if b < 9000 then 2.12970e-26
  else if b < 9500 then 2.44532e-27
  else if b < 10000 then 2.97001e-28
  else if b < 10500 then 3.78493e-29
  else if b < 11000 then 5.10153e-30
  else if b < 11500 then 7.14264e-31
  else if b < 12000 then 1.04329e-31
  else if b < 12500 then 1.59755e-32
  else if b < 13000 then 2.53362e-33
  else if b < 13500 then 4.13554e-34
  else if b < 14000 then 7.21538e-35
  else if b < 15000 then 1.22655e-35
  else if b < 16000 then 4.10696e-37
  else if b < 17000 then 1.51402e-38
  else if b < 18000 then 6.20397e-40
  else if b < 19000 then 2.82833e-41
  else if b < 20000 then 1.36785e-42
  else if b < 21000 then 7.16209e-44
  else if b < 22000 then 4.11842e-45
  else if b < 23000 then 2.43916e-46
  else if b < 24000 then 1.56474e-47
  else if b < 25000 then 1.07022e-48
  else 7.57240e-50

noncomputable def BKLNW.a₁ (b : ℝ) : ℝ :=
  if b ≤ 38 * log 10 then 1 + 1.93378e-8 else 1 + BKLNW.ε (b / 2)

noncomputable def BKLNW.a₂ (b : ℝ) : ℝ :=
  (1 + 1.93378e-8) * (max (BKLNW.f (exp b)) (BKLNW.f (⌊b / (log 2)⌋ + 1)))
