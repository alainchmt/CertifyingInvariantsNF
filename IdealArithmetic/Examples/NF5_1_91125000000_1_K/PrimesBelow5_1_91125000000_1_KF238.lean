
import IdealArithmetic.Examples.NF5_1_91125000000_1_K.RI5_1_91125000000_1_K
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 

instance hp18787 : Fact (Nat.Prime 18787) := {out := by norm_num}

def I18787N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18787, 0, 0, 0, 0], ![1287, 10203, 1, 0, 0]] i)))

def I18787N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18787, 0, 0, 0, 0], ![12819, 1156, 8584, 2, 0]] i)))

def P18787P0 : CertificateIrreducibleZModOfList' 18787 2 2 14 [1287, 10203, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8584, 18786], [0, 1]]
 g := ![![[7803, 3633], [13872, 17470], [8544], [8635], [15666], [16854, 6371], [4972, 12203], [6574], [5771, 16280], [17920], [4098], [7062, 15640], [2442], [1]], ![[7055, 15154], [18518, 1317], [8544], [8635], [15666], [16561, 12416], [17999, 6584], [6574], [15585, 2507], [17920], [4098], [8920, 3147], [2442], [1]]]
 h' := ![![[8584, 18786], [13173, 14645], [12285, 4475], [9066, 18231], [16108, 2698], [7887, 9221], [7403, 8443], [1200, 5985], [12375, 5131], [6637, 5034], [2930, 15935], [4114, 15379], [16475, 12919], [17500, 8584], [0, 1]], ![[0, 1], [3249, 4142], [6270, 14312], [8260, 556], [11369, 16089], [11320, 9566], [1869, 10344], [12782, 12802], [1364, 13656], [8393, 13753], [823, 2852], [1201, 3408], [13510, 5868], [1155, 10203], [8584, 18786]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11636]]
 b := ![[], [15854, 5818]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P18787P1 : CertificateIrreducibleZModOfList' 18787 3 2 14 [12819, 1155, 8584, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5120, 9488, 11657], [5083, 9298, 7130], [0, 1]]
 g := ![![[706, 3120, 18386], [571, 8478, 5479], [16689, 9806], [13398, 12678], [6193, 11533], [5878, 13453, 17749], [1863, 13369, 2166], [9652, 12319], [12316, 5693, 3384], [8095, 14561], [6480, 15301], [15884, 1260, 3113], [10203, 1], []], ![[4630, 13663, 10917, 18402], [11418, 7455, 18769, 16000], [13203, 1783], [1377, 13800], [13984, 11099], [7168, 2105, 13869, 17948], [9824, 3125, 2973, 6222], [4272, 13677], [8603, 11377, 16400, 15418], [6989, 16548], [5502, 18069], [14263, 15879, 11579, 14677], [13442, 13817], [3032, 18065]], ![[16336, 18467, 14169, 7414], [17266, 3177, 14395, 15651], [7352, 13989], [12487, 1504], [6730, 8955], [13480, 7506, 11799, 8888], [7252, 6872, 16035, 18448], [16037, 10035], [5179, 10270, 4424, 15323], [5408, 5821], [7802, 6516], [9042, 15509, 14894, 11353], [517, 13627], [7559, 18065]]]
 h' := ![![[5120, 9488, 11657], [7281, 7224, 1520], [14090, 11304, 17449], [12037, 17787, 15571], [7702, 4730, 7752], [4575, 13437, 7594], [15267, 5743, 16506], [13438, 14100, 9521], [7144, 2452, 13367], [865, 14346, 15628], [15118, 4409, 1403], [15297, 2705, 6909], [2837, 952, 1287], [0, 0, 1], [0, 1]], ![[5083, 9298, 7130], [5085, 8023, 11970], [10765, 3028, 13767], [11784, 16828, 16263], [1081, 2822, 8929], [15237, 783, 15356], [13745, 68, 9855], [13667, 18274, 16938], [7354, 10884, 18298], [8985, 15088, 18721], [10261, 1643, 1397], [8994, 13510, 14728], [5634, 5034, 12341], [9630, 14079, 9298], [5120, 9488, 11657]], ![[0, 1], [8531, 3540, 5297], [11201, 4455, 6358], [18220, 2959, 5740], [689, 11235, 2106], [9582, 4567, 14624], [15465, 12976, 11213], [2706, 5200, 11115], [17659, 5451, 5909], [10579, 8140, 3225], [7463, 12735, 15987], [14037, 2572, 15937], [1218, 12801, 5159], [9289, 4708, 9488], [5083, 9298, 7130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7863, 1171], []]
 b := ![[], [5074, 9802, 12271], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A18787 : FactorsPolyZMod [-15720, -525, -100, 0, 0, 1] 18787 2 where
 D := ![[1287, 10203, 1], [12819, 1155, 8584, 1]]; D' := ![[1287, 10203, 1], [12819, 1155, 8584, 1]]
 heqm := by decide
 hProd := by decide
 s := ![14, 14]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P18787P0
  | 1 => exact P18787P1

def C187870 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A18787.D 0) 18787 where
  n := 2
  w := ![![18787, 0, 0, 0, 0], ![1287, 10203, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C187871 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A18787.D 1) 18787 where
  n := 3
  w := ![![18787, 0, 0, 0, 0], ![12819, 1156, 8584, 2, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K18787 : KummerData 18787 ![I18787N0, I18787N1] ![352951369, 6630897369403] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A18787
  C := by
    intro i
    match i with
    | 0 => exact C187870
    | 1 => exact C187871
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 18787 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB18792I238_primes (p : ℕ) :
  p ∈ Set.range ![18787] ↔ Nat.Prime p ∧ 18773 < p ∧ p ≤ 18791 := by
  rw [← List.mem_ofFn']
  convert primes_range 18773 18791 (by omega)
  decide

def PB18792I238 : PrimesBelowBoundCertificateInterval O 18773 18791 18792 where
  m := 1
  g := ![2]
  P := ![18787]
  hP := PB18792I238_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I18787N0, I18787N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · convert (containsPrimesAbove_of_KummerData K18787) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![352951369, 6630897369403]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact (card_quot_of_KummerData K18787)
  β := ![]
  Il := ![[]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
