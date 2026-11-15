import RSBounds.RS75ScalarNumericsBase
import RSBounds.RS75Parameters
import RSBounds.RS75Polynomial
import RSBounds.SmallTotientProduct

/-! Exact radical/logarithm certificates for the RS75 zero-free scalar assembly.
Generated scalar data are checked by the ordinary Lean kernel, using the existing
logarithm and interval soundness proofs. No zeta value is assumed or certified here. -/
namespace TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
open RS75ScalarNumerics
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def a0 : ℝ := 11.1859355312082048
def a1 : ℝ := 19.073344004352
def A0 : ℝ := 36.506331844352
def k0 : ℝ := 1 / Real.sqrt 5
def h : ℝ := (1 - k0) * A0 / 2
def v : ℝ := 2 * Real.sqrt a0 * (Real.sqrt a1 - Real.sqrt a0) / ((1 - k0) * A0)
def R1 : ℝ := (1 - k0) * A0 / (2 * (Real.sqrt a1 - Real.sqrt a0) ^ 2)
def heightRatio : ℝ := v / Real.log ((1894439 : ℝ) / 17)
def D : ℝ := ∑ k ∈ Finset.Icc 1 4, RS75Polynomial.coeff k * Real.log (2 * Real.pi / k)
def H : ℝ := ∑ k ∈ Finset.Icc 1 4, RS75Polynomial.coeff k / (k : ℝ) ^ 2

def c0 : ℝ := -a0 * 0.5772156646 - 52.38865 / 2 + h * Real.log 17 +
 k0 * (-a0 * 1.1398 + 52.38865 / 2) - k0 * A0 / 2 * (4 / 5) * v
def c1 : ℝ := a0 * 0.2 + k0 * (4 / 5) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * a0 * 3.3606 - k0 * A0 / 2 * (-26 / 25) * v - k0 * A0 / 2 * (4 / 5) * Real.log 17
def c2 : ℝ := k0 * (-26 / 25) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * (4 / 5) * a0 * 3.3606 - k0 * A0 / 2 * (6 / 5) * v - k0 * A0 / 2 * (-26 / 25) * Real.log 17
def c3 : ℝ := k0 * (6 / 5) * (-a0 * 1.1398 + 52.38865 / 2) +
 k0 * (-26 / 25) * a0 * 3.3606 - k0 * A0 / 2 * (6 / 5) * Real.log 17
def c4 : ℝ := k0 * (6 / 5) * a0 * 3.3606

private def n0 : Expr := .old (.rat (873901213375641/78125000000000))
private def n1 : Expr := .old (.rat (74505250017/3906250000))
private def n2 : Expr := .old (.rat (142602858767/3906250000))
private def n3 : Expr := .old (.rat (1))
private def n4 : Expr := .sqrtRat (5) (2795084971874737/1250000000000000) (22360679774997897/10000000000000000)
private def n5 : Expr := .inv n4
private def n6 : Expr := .mul n3 n5
private def n7 : Expr := .sub n3 n6
private def n8 : Expr := .mul n7 n2
private def n9 : Expr := .old (.rat (2))
private def n10 : Expr := .inv n9
private def n11 : Expr := .mul n8 n10
private def n12 : Expr := .sqrtRat (873901213375641/78125000000000) (33445381641129773/10000000000000000) (16722690820564887/5000000000000000)
private def n13 : Expr := .sqrtRat (74505250017/3906250000) (43673039743475607/10000000000000000) (5459129967934451/1250000000000000)
private def n14 : Expr := .mul n9 n12
private def n15 : Expr := .sub n13 n12
private def n16 : Expr := .mul n14 n15
private def n17 : Expr := .inv n8
private def n18 : Expr := .mul n16 n17
private def n19 : Expr := .pow n15 2
private def n20 : Expr := .mul n9 n19
private def n21 : Expr := .inv n20
private def n22 : Expr := .mul n8 n21
private def n23 : Expr := .old (.log ⟨4, 16, 1⟩ ⟨4, 16, 1⟩ (.rat (17)))
private def n24 : Expr := .old (.log ⟨16, 1114112, 780327⟩ ⟨16, 1114112, 780327⟩ (.rat (1894439/17)))
private def n25 : Expr := .inv n24
private def n26 : Expr := .mul n18 n25
private def n27 : Expr := .old (.rat (1047773/40000))
private def n28 : Expr := .old (.rat (5699/5000))
private def n29 : Expr := .mul n0 n28
private def n30 : Expr := .sub n27 n29
private def n31 : Expr := .old (.rat (0))
private def n32 : Expr := .old (.rat (2886078323/5000000000))
private def n33 : Expr := .mul n0 n32
private def n34 : Expr := .sub n31 n33
private def n35 : Expr := .sub n34 n27
private def n36 : Expr := .mul n11 n23
private def n37 : Expr := .add n35 n36
private def n38 : Expr := .mul n6 n3
private def n39 : Expr := .mul n38 n30
private def n40 : Expr := .add n37 n39
private def n41 : Expr := .mul n6 n2
private def n42 : Expr := .mul n41 n10
private def n43 : Expr := .old (.rat (4/5))
private def n44 : Expr := .mul n42 n43
private def n45 : Expr := .mul n44 n18
private def n46 : Expr := .mul n45 n3
private def n47 : Expr := .sub n40 n46
private def n48 : Expr := .old (.rat (1/5))
private def n49 : Expr := .mul n0 n48
private def n50 : Expr := .add n31 n49
private def n51 : Expr := .mul n6 n43
private def n52 : Expr := .mul n51 n30
private def n53 : Expr := .add n50 n52
private def n54 : Expr := .mul n38 n0
private def n55 : Expr := .old (.rat (16803/5000))
private def n56 : Expr := .mul n54 n55
private def n57 : Expr := .add n53 n56
private def n58 : Expr := .old (.rat (-26/25))
private def n59 : Expr := .mul n42 n58
private def n60 : Expr := .mul n59 n18
private def n61 : Expr := .mul n60 n3
private def n62 : Expr := .sub n57 n61
private def n63 : Expr := .mul n44 n23
private def n64 : Expr := .sub n62 n63
private def n65 : Expr := .mul n6 n58
private def n66 : Expr := .mul n65 n30
private def n67 : Expr := .add n31 n66
private def n68 : Expr := .mul n51 n0
private def n69 : Expr := .mul n68 n55
private def n70 : Expr := .add n67 n69
private def n71 : Expr := .old (.rat (6/5))
private def n72 : Expr := .mul n42 n71
private def n73 : Expr := .mul n72 n18
private def n74 : Expr := .mul n73 n3
private def n75 : Expr := .sub n70 n74
private def n76 : Expr := .mul n59 n23
private def n77 : Expr := .sub n75 n76
private def n78 : Expr := .mul n6 n71
private def n79 : Expr := .mul n78 n30
private def n80 : Expr := .add n31 n79
private def n81 : Expr := .mul n65 n0
private def n82 : Expr := .mul n81 n55
private def n83 : Expr := .add n80 n82
private def n84 : Expr := .mul n72 n23
private def n85 : Expr := .sub n83 n84
private def n86 : Expr := .mul n78 n0
private def n87 : Expr := .mul n86 n55
private def n88 : Expr := .add n31 n87
private def n89 : Expr := .old (.log ⟨2, 4000000000000, 2283185307179⟩ ⟨2, 200000000000, 114159265359⟩ (.mul (.mul (.rat 2) .pi) (.rat (1))))
private def n90 : Expr := .mul n1 n89
private def n91 : Expr := .add n31 n90
private def n92 : Expr := .old (.rat (36488087/3125000))
private def n93 : Expr := .old (.log ⟨1, 2000000000000, 1141592653589⟩ ⟨1, 200000000000, 114159265359⟩ (.mul (.mul (.rat 2) .pi) (.rat (1/2))))
private def n94 : Expr := .mul n92 n93
private def n95 : Expr := .add n91 n94
private def n96 : Expr := .old (.rat (2973/625))
private def n97 : Expr := .old (.log ⟨1, 2000000000000, 94395102393⟩ ⟨1, 1000000000000, 47197551197⟩ (.mul (.mul (.rat 2) .pi) (.rat (1/3))))
private def n98 : Expr := .mul n96 n97
private def n99 : Expr := .add n95 n98
private def n100 : Expr := .old (.log ⟨0, 500000000000, 285398163397⟩ ⟨0, 200000000000, 114159265359⟩ (.mul (.mul (.rat 2) .pi) (.rat (1/4))))
private def n101 : Expr := .mul n3 n100
private def n102 : Expr := .add n99 n101

private def vCertificate : Expr := n18
private theorem vCertificate_checked : vCertificate.check = true := by decide +kernel
private theorem vCertificate_eval : vCertificate.eval = v := by
  norm_num [vCertificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem v_lower : (339/1000 : ℝ) < v := by
  have hb : (339/1000 : ℚ) < vCertificate.bounds.lo := by decide +kernel
  have hh := Expr.lt_eval vCertificate_checked hb
  rw [vCertificate_eval] at hh
  norm_num at hh ⊢
  exact hh

theorem v_upper : v < (17/50 : ℝ) := by
  have hb : vCertificate.bounds.hi < (17/50 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt vCertificate_checked hb
  rw [vCertificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def R1Certificate : Expr := n22
private theorem R1Certificate_checked : R1Certificate.check = true := by decide +kernel
private theorem R1Certificate_eval : R1Certificate.eval = R1 := by
  norm_num [R1Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem R1_lower : (6028693/625000 : ℝ) < R1 := by
  have hb : (6028693/625000 : ℚ) < R1Certificate.bounds.lo := by decide +kernel
  have hh := Expr.lt_eval R1Certificate_checked hb
  rw [R1Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh

theorem R1_upper : R1 < (9645908801/1000000000 : ℝ) := by
  have hb : R1Certificate.bounds.hi < (9645908801/1000000000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt R1Certificate_checked hb
  rw [R1Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def heightRatioCertificate : Expr := n26
private theorem heightRatioCertificate_checked : heightRatioCertificate.check = true := by decide +kernel
private theorem heightRatioCertificate_eval : heightRatioCertificate.eval = heightRatio := by
  norm_num [heightRatioCertificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem heightRatio_lower : (0 : ℝ) < heightRatio := by
  have hb : (0 : ℚ) < heightRatioCertificate.bounds.lo := by decide +kernel
  have hh := Expr.lt_eval heightRatioCertificate_checked hb
  rw [heightRatioCertificate_eval] at hh
  norm_num at hh ⊢
  exact hh

theorem heightRatio_upper : heightRatio < (7293/250000 : ℝ) := by
  have hb : heightRatioCertificate.bounds.hi < (7293/250000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt heightRatioCertificate_checked hb
  rw [heightRatioCertificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def DCertificate : Expr := n102
private theorem DCertificate_checked : DCertificate.check = true := by decide +kernel
private theorem DCertificate_eval : DCertificate.eval = D := by
  norm_num [DCertificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem D_lower : (1047773/20000 : ℝ) < D := by
  have hb : (1047773/20000 : ℚ) < DCertificate.bounds.lo := by decide +kernel
  have hh := Expr.lt_eval DCertificate_checked hb
  rw [DCertificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def c0Certificate : Expr := n47
private theorem c0Certificate_checked : c0Certificate.check = true := by decide +kernel
private theorem c0Certificate_eval : c0Certificate.eval = c0 := by
  norm_num [c0Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem c0_upper : c0 < (-26491/100000 : ℝ) := by
  have hb : c0Certificate.bounds.hi < (-26491/100000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt c0Certificate_checked hb
  rw [c0Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def c1Certificate : Expr := n64
private theorem c1Certificate_checked : c1Certificate.check = true := by decide +kernel
private theorem c1Certificate_eval : c1Certificate.eval = c1 := by
  norm_num [c1Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem c1_upper : c1 < (823461/100000 : ℝ) := by
  have hb : c1Certificate.bounds.hi < (823461/100000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt c1Certificate_checked hb
  rw [c1Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def c2Certificate : Expr := n77
private theorem c2Certificate_checked : c2Certificate.check = true := by decide +kernel
private theorem c2Certificate_eval : c2Certificate.eval = c2 := by
  norm_num [c2Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem c2_upper : c2 < (2792797/100000 : ℝ) := by
  have hb : c2Certificate.bounds.hi < (2792797/100000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt c2Certificate_checked hb
  rw [c2Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def c3Certificate : Expr := n85
private theorem c3Certificate_checked : c3Certificate.check = true := by decide +kernel
private theorem c3Certificate_eval : c3Certificate.eval = c3 := by
  norm_num [c3Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem c3_upper : c3 < (0 : ℝ) := by
  have hb : c3Certificate.bounds.hi < (0 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt c3Certificate_checked hb
  rw [c3Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


private def c4Certificate : Expr := n88
private theorem c4Certificate_checked : c4Certificate.check = true := by decide +kernel
private theorem c4Certificate_eval : c4Certificate.eval = c4 := by
  norm_num [c4Certificate, Expr.eval, QuarticBudgetNumerics.Expr.eval, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55, n56, n57, n58, n59, n60, n61, n62, n63, n64, n65, n66, n67, n68, n69, n70, n71, n72, n73, n74, n75, n76, n77, n78, n79, n80, n81, n82, n83, n84, n85, n86, n87, n88, n89, n90, n91, n92, n93, n94, n95, n96, n97, n98, n99, n100, n101, n102,
    a0, a1, A0, k0, h, v, R1, heightRatio, D, c0, c1, c2, c3, c4, RS75Polynomial.coeff, Finset.sum_Icc_succ_top, div_eq_mul_inv] <;> ring

theorem c4_upper : c4 < (201737/10000 : ℝ) := by
  have hb : c4Certificate.bounds.hi < (201737/10000 : ℚ) := by decide +kernel
  have hh := Expr.eval_lt c4Certificate_checked hb
  rw [c4Certificate_eval] at hh
  norm_num at hh ⊢
  exact hh


end
end TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
