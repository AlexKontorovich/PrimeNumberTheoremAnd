import RSBounds.BacklundRightArcNumericsBase

/-! Generated rational certificates for 17 quadrature nodes.
All roots, cosine recurrences, and exponential Taylor comparisons are checked
by the Lean kernel. The generating Python calculation is not trusted. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Finset
namespace TernaryGoldbach.RSBounds.BacklundRightArc

private def roots_0 : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]

private theorem log_sample_0 : logZeta (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 164) (bs := roots_0) (bTail := 1313901)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_0, Finset.sum_range_succ]

private theorem sigma_sample_0 : (164 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 0) := by
  have h := sigma_sample_lower_of_cos_cert (i := 0) (p := 164)
    (a := 1000000000000) (bs := [1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000, 1000000000000])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_1 : List ℕ := [100000000, 16928194, 5989309, 2865637, 1617667, 1013882, 683024, 485100, 358718, 273841, 214501, 171631, 139804, 115623, 96887, 82118]

private theorem log_sample_1 : logZeta (164 / 64) ≤ (276700 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 164) (bs := roots_1) (bTail := 1313901)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_1, Finset.sum_range_succ]

private theorem sigma_sample_1 : (164 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 1) := by
  have h := sigma_sample_lower_of_cos_cert (i := 1) (p := 164)
    (a := 999999926465) (bs := [999999705860, 999998823440, 999995293762, 999981175092, 999924701076, 999698815643, 998795443996, 995184677894])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_2 : List ℕ := [100000000, 17298873, 6198503, 2992510, 1701109, 1072271, 725847, 517670, 384214, 294272, 231193, 185490, 151471, 125563, 105443, 89551]

private theorem log_sample_2 : logZeta (162 / 64) ≤ (285253 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 162) (bs := roots_2) (bTail := 1432819)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_2, Finset.sum_range_succ]

private theorem sigma_sample_2 : (162 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 2) := by
  have h := sigma_sample_lower_of_cos_cert (i := 2) (p := 162)
    (a := 999999705862) (bs := [999998823448, 999995293794, 999981175220, 999924701588, 999698817691, 998795452185, 995184710610, 980785216463])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_3 : List ℕ := [100000000, 17677669, 6415002, 3125000, 1788854, 1134023, 771356, 552427, 411522, 316227, 249182, 200468, 164112, 136357, 114755, 97656]

private theorem log_sample_3 : logZeta (160 / 64) ≤ (294135 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 160) (bs := roots_3) (bTail := 1562500)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_3, Finset.sum_range_succ]

private theorem sigma_sample_3 : (160 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 3) := by
  have h := sigma_sample_lower_of_cos_cert (i := 3) (p := 160)
    (a := 999999338191) (bs := [999997352764, 999989411070, 999957644504, 999830581603, 999322383817, 997290453595, 989176497663, 956940287057])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_4 : List ℕ := [100000000, 18064760, 6639064, 3263355, 1881125, 1199331, 819717, 589517, 440771, 339820, 268572, 216656, 177808, 148080, 124889, 106494]

private theorem log_sample_4 : logZeta (158 / 64) ≤ (303361 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 158) (bs := roots_4) (bTail := 1703919)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_4, Finset.sum_range_succ]

private theorem sigma_sample_4 : (158 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 4) := by
  have h := sigma_sample_lower_of_cos_cert (i := 4) (p := 158)
    (a := 999998823451) (bs := [999995293806, 999981175268, 999924701780, 999698818459, 998795455256, 995184722880, 980785265307, 923879473286])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_5 : List ℕ := [100000000, 18864555, 7110939, 3558714, 2080192, 1341447, 925726, 671335, 505654, 392418, 311995, 253058, 208724, 174634, 147921, 126644]

private theorem log_sample_5 : logZeta (154 / 64) ≤ (322917 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 154) (bs := roots_5) (bTail := 2026312)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_5, Finset.sum_range_succ]

private theorem sigma_sample_5 : (154 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 5) := by
  have h := sigma_sample_lower_of_cos_cert (i := 5) (p := 154)
    (a := 999998161642) (bs := [999992646574, 999970586404, 999882347346, 999529417068, 998118111168, 992479527683, 970031225739, 881921157817])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_6 : List ℕ := [100000000, 19699760, 7616352, 3880805, 2300324, 1500403, 1045445, 764509, 580088, 453158, 362439, 295575, 245016, 205950, 175200, 150606]

private theorem log_sample_6 : logZeta (150 / 64) ≤ (344080 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 150) (bs := roots_6) (bTail := 2409705)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_6, Finset.sum_range_succ]

private theorem sigma_sample_6 : (150 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 6) := by
  have h := sigma_sample_lower_of_cos_cert (i := 6) (p := 150)
    (a := 999997352765) (bs := [999989411074, 999957644520, 999830581667, 999322384073, 997290454618, 989176501744, 956940303204, 831469487792])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_7 : List ℕ := [100000000, 20795957, 8298931, 4324718, 2608531, 1725842, 1217095, 899366, 688722, 542469, 437113, 358905, 299379, 253106, 216480, 187031]

private theorem log_sample_7 : logZeta (145 / 64) ≤ (373068 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 145) (bs := roots_7) (bTail := 2992511)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_7, Finset.sum_range_succ]

private theorem sigma_sample_7 : (145 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 7) := by
  have h := sigma_sample_lower_of_cos_cert (i := 7) (p := 145)
    (a := 999996396819) (bs := [999985587301, 999942349619, 999769405123, 999077726839, 996312608531, 985277627835, 941544007824, 773010237338])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_8 : List ℕ := [100000000, 22192206, 9199246, 4924940, 3033363, 2041515, 1460671, 1092952, 846261, 673170, 547299, 453057, 380762, 324155, 279046, 242550]

private theorem log_sample_8 : logZeta (139 / 64) ≤ (412130 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 139) (bs := roots_8) (bTail := 3880806)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_8, Finset.sum_range_succ]

private theorem sigma_sample_8 : (139 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 8) := by
  have h := sigma_sample_lower_of_cos_cert (i := 8) (p := 139)
    (a := 999995293804) (bs := [999981175260, 999924701748, 999698818331, 998795454744, 995184720834, 980785257162, 923879441332, 707106444231])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_9 : List ℕ := [100000000, 23682199, 10197234, 5608465, 3527385, 2414929, 1752994, 1328208, 1039835, 835362, 685260, 571908, 484268, 415147, 359695, 314548]

private theorem log_sample_9 : logZeta (133 / 64) ≤ (456702 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 133) (bs := roots_9) (bTail := 5032783)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_9, Finset.sum_range_succ]

private theorem sigma_sample_9 : (133 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 9) := by
  have h := sigma_sample_lower_of_cos_cert (i := 9) (p := 133)
    (a := 999994043721) (bs := [999976174954, 999904700951, 999618821967, 998475578461, 993906961566, 975702096498, 903989162221, 634392810826])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_10 : List ℕ := [100000000, 25547428, 11499197, 6526711, 4206324, 2937749, 2168768, 1667406, 1322315, 1074607, 890754, 750519, 641097, 554064, 483693, 425979]

private theorem log_sample_10 : logZeta (126 / 64) ≤ (517200 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 126) (bs := roots_10) (bTail := 6815674)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_10, Finset.sum_range_succ]

private theorem sigma_sample_10 : (126 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 10) := by
  have h := sigma_sample_lower_of_cos_cert (i := 10) (p := 126)
    (a := 999992646570) (bs := [999970586388, 999882347282, 999529416812, 998118110145, 992479523598, 970031209522, 881921094893, 555569635234])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_11 : List ℕ := [100000000, 27559564, 12967392, 7595295, 5015943, 3573756, 2683155, 2093230, 1681532, 1382372, 1157871, 984911, 848714, 739465, 650437, 576885]

private theorem log_sample_11 : logZeta (119 / 64) ≤ (589182 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 119) (bs := roots_11) (bTail := 9230164)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_11, Finset.sum_range_succ]

private theorem sigma_sample_11 : (119 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 11) := by
  have h := sigma_sample_lower_of_cos_cert (i := 11) (p := 119)
    (a := 999991102349) (bs := [999964409554, 999857640749, 999430603528, 997723062536, 990902619032, 963776000808, 857728359466, 471395877264])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_12 : List ℕ := [100000000, 29730177, 14623044, 8838834, 5981395, 4347457, 3319544, 2627801, 2138334, 1778279, 1505091, 1292506, 1123567, 986906, 874662, 781250]

private theorem log_sample_12 : logZeta (112 / 64) ≤ (676082 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 112) (bs := roots_12) (bTail := 12500000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_12, Finset.sum_range_succ]

private theorem sigma_sample_12 : (112 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 12) := by
  have h := sigma_sample_lower_of_cos_cert (i := 12) (p := 112)
    (a := 999989411060) (bs := [999957644464, 999830581443, 999322383177, 997290451037, 989176487459, 956940246683, 831469271443, 382682298707])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_13 : List ℕ := [100000000, 32420988, 16775596, 10511205, 7314316, 5438814, 4233657, 3407836, 2814206, 2371373, 2031126, 1763317, 1548253, 1372593, 1227020, 1104854]

private theorem log_sample_13 : logZeta (104 / 64) ≤ (800295 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 104) (bs := roots_13) (bTail := 17677670)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_13, Finset.sum_range_succ]

private theorem sigma_sample_13 : (104 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 13) := by
  have h := sigma_sample_lower_of_cos_cert (i := 13) (p := 104)
    (a := 999987572703) (bs := [999950291120, 999801169421, 999204756751, 996820291827, 987301388396, 949528063057, 803207085065, 290283242997])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_14 : List ℕ := [100000000, 35355339, 19245008, 12500000, 8944271, 6804138, 5399492, 4419417, 3703703, 3162277, 2741012, 2405626, 2133462, 1909008, 1721325, 1562500]

private theorem log_sample_14 : logZeta (96 / 64) ≤ (963201 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 96) (bs := roots_14) (bTail := 25000000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_14, Finset.sum_range_succ]

private theorem sigma_sample_14 : (96 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 14) := by
  have h := sigma_sample_lower_of_cos_cert (i := 14) (p := 96)
    (a := 999985587277) (bs := [999942349523, 999769404739, 999077725304, 996312602397, 985277603390, 941543911483, 773009874501, 195088532152])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_15 : List ℕ := [100000000, 38555270, 22077926, 14865088, 10937454, 8512204, 6886367, 5731275, 4874348, 4216965, 3699006, 3281903, 2939868, 2655057, 2414763, 2209708]

private theorem log_sample_15 : logZeta (88 / 64) ≤ (1188266 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 88) (bs := roots_15) (bTail := 35355340)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_15, Finset.sum_range_succ]

private theorem sigma_sample_15 : (88 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 15) := by
  have h := sigma_sample_lower_of_cos_cert (i := 15) (p := 88)
    (a := 999983454782) (bs := [999933819675, 999735287459, 998941289981, 995767401657, 983105436405, 932992598178, 740950376509, 98014920897])
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num [cosEnd])
  simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h

private def roots_16 : List ℕ := [100000000, 42044820, 25327856, 17677669, 13374806, 10649051, 8782687, 7432544, 6415002, 5623413, 4991822, 4477374, 4051079, 3692665, 3387551, 3125000]

private theorem log_sample_16 : logZeta (80 / 64) ≤ (1528345 : ℝ) / 1000000 := by
  apply logZeta_le_of_root_cert (p := 80) (bs := roots_16) (bTail := 50000000)
  · norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num
  · norm_num [roots_16, Finset.sum_range_succ]

private theorem sigma_sample_16 : (80 : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * 16) := by
  rw [show Real.pi / 32 * 16 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  norm_num

noncomputable def sampleP : ℕ → ℕ
  | 0 => 164
  | 1 => 164
  | 2 => 162
  | 3 => 160
  | 4 => 158
  | 5 => 154
  | 6 => 150
  | 7 => 145
  | 8 => 139
  | 9 => 133
  | 10 => 126
  | 11 => 119
  | 12 => 112
  | 13 => 104
  | 14 => 96
  | 15 => 88
  | 16 => 80
  | _ => 80

noncomputable def sampleB : ℕ → ℝ
  | 0 => 276700 / 1000000
  | 1 => 276700 / 1000000
  | 2 => 285253 / 1000000
  | 3 => 294135 / 1000000
  | 4 => 303361 / 1000000
  | 5 => 322917 / 1000000
  | 6 => 344080 / 1000000
  | 7 => 373068 / 1000000
  | 8 => 412130 / 1000000
  | 9 => 456702 / 1000000
  | 10 => 517200 / 1000000
  | 11 => 589182 / 1000000
  | 12 => 676082 / 1000000
  | 13 => 800295 / 1000000
  | 14 => 963201 / 1000000
  | 15 => 1188266 / 1000000
  | 16 => 1528345 / 1000000
  | _ => 0

lemma sampleP_gt_one (i : ℕ) (hi : i ≤ 16) : 1 < (sampleP i : ℝ) / 64 := by
  interval_cases i <;> norm_num [sampleP]

lemma sample_log_bound (i : ℕ) (hi : i ≤ 16) : logZeta ((sampleP i : ℝ) / 64) ≤ sampleB i := by
  interval_cases i
  · exact log_sample_0
  · exact log_sample_1
  · exact log_sample_2
  · exact log_sample_3
  · exact log_sample_4
  · exact log_sample_5
  · exact log_sample_6
  · exact log_sample_7
  · exact log_sample_8
  · exact log_sample_9
  · exact log_sample_10
  · exact log_sample_11
  · exact log_sample_12
  · exact log_sample_13
  · exact log_sample_14
  · exact log_sample_15
  · exact log_sample_16

lemma sample_sigma_lower (i : ℕ) (hi : i ≤ 16) : (sampleP i : ℝ) / 64 ≤
    5 / 4 + (33 / 25) * Real.cos (Real.pi / 32 * i) := by
  interval_cases i
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_0
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_1
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_2
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_3
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_4
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_5
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_6
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_7
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_8
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_9
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_10
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_11
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_12
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_13
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_14
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_15
  · simpa only [sampleP, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using sigma_sample_16

lemma sample_arc_bound (i : ℕ) (hi : i ≤ 16) :
    arcFunction (Real.pi / 32 * i) ≤ sampleB i := by
  have hiR : (i : ℝ) ≤ 16 := by exact_mod_cast hi
  have hmem : Real.pi / 32 * i ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hiR Real.pi_pos.le]
  exact (antitoneOn_logZeta (sampleP_gt_one i hi) (arc_sigma_gt_one hmem)
    (sample_sigma_lower i hi)).trans (sample_log_bound i hi)

/-- A certified bound stronger than the printed 0.1367 in Backlund (1918), p. 373. -/
theorem right_arc_integral_lt :
    (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi) < 0.1361 := by
  have hs : (∑ i ∈ Finset.range 16,
      (arcFunction (Real.pi / 32 * i) + arcFunction (Real.pi / 32 * ((i : ℝ) + 1))) / 2) ≤
      ∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < 16 := Finset.mem_range.mp hi
    have h0 := sample_arc_bound i (by omega)
    have h1 := sample_arc_bound (i + 1) (by omega)
    push_cast at h1
    linarith
  have hn : (∑ i ∈ Finset.range 16, (sampleB i + sampleB (i + 1)) / 2) / 64 < (0.1361 : ℝ) := by
    norm_num [sampleB, Finset.sum_range_succ]
  exact (right_arc_le_samples.trans (div_le_div_of_nonneg_right hs (by norm_num))).trans_lt hn

end TernaryGoldbach.RSBounds.BacklundRightArc
