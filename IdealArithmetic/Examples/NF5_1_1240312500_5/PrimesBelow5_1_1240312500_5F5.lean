
import IdealArithmetic.Examples.NF5_1_1240312500_5.PrimesBelow5_1_1240312500_5F4

open Classical Polynomial

noncomputable section 
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}
def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate O ℤ timesTableO I199N0
 ![![199, 0, 0, 0, 0]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 312079600999 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI199N0)

def MemCI199N0 : IdealMemCertificate O ℤ B I199N0
  ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]] ![136973790657782, 1818710939846, -13958585910608, 33662285360334, -42523022208912] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI199N0
 g := ![688310505818, 9139250954, -70143647792, 169157212866, -213683528688]
 hmem := by decide

def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [38, 67, 153, 26, 91, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 163, 102, 165, 24], [109, 180, 105, 80, 42], [96, 125, 75, 118, 77], [83, 128, 116, 35, 56], [0, 1]]
 g := ![![[99, 170, 117, 165, 177], [60, 38, 138, 178, 46], [102, 130, 82, 10, 162], [50, 17, 12, 100], [82, 46, 160, 62], [108, 1], []],![[194, 117, 147, 109, 170, 57, 94, 88], [105, 176, 47, 125, 198, 192, 27, 150], [159, 82, 133, 128, 82, 140, 155, 176], [157, 26, 60, 130], [94, 42, 116, 175], [155, 154, 6, 104], [26, 62, 147, 49, 185, 63, 47, 93]],![[132, 174, 137, 64, 141, 119, 89, 85], [133, 61, 113, 150, 23, 71, 106, 171], [38, 150, 175, 105, 43, 76, 41, 166], [98, 191, 135, 169], [161, 193, 134, 196], [79, 54, 1, 145], [23, 143, 99, 15, 92, 136, 0, 60]],![[12, 85, 2, 92, 157, 35, 143, 77], [149, 157, 197, 185, 18, 38, 191, 71], [52, 98, 187, 70, 92, 108, 170, 135], [92, 100, 133, 112], [151, 131, 54, 155], [101, 60, 8, 104], [148, 163, 128, 134, 183, 151, 143, 27]],![[161, 124, 130, 25, 84, 77, 51, 124], [130, 77, 58, 149, 168, 123, 110, 70], [50, 193, 156, 69, 39, 51, 143, 115], [98, 182, 151, 106], [8, 130], [36, 21, 145, 145], [158, 70, 116, 54, 36, 46, 171, 98]]]
 h' := ![![[19, 163, 102, 165, 24], [108, 178, 72, 130, 133], [104, 191, 107, 55, 65], [5, 147, 129, 74, 19], [121, 138, 187, 22, 189], [75, 89, 125, 24, 96], [0, 0, 0, 1], [0, 1]],![[109, 180, 105, 80, 42], [17, 174, 47, 43, 104], [186, 80, 184, 167, 97], [29, 46, 46, 131, 109], [194, 178, 61, 158, 54], [130, 178, 100, 114, 162], [100, 97, 77, 8, 169], [19, 163, 102, 165, 24]],![[96, 125, 75, 118, 77], [88, 136, 174, 161, 132], [192, 126, 157, 178, 27], [183, 90, 174, 166, 130], [153, 104, 158, 15, 13], [163, 120, 31, 59, 14], [58, 169, 15, 159, 44], [109, 180, 105, 80, 42]],![[83, 128, 116, 35, 56], [29, 117, 122, 56, 1], [168, 1, 165, 74, 171], [126, 197, 70, 148, 81], [144, 141, 128, 153, 50], [67, 84, 154, 147, 126], [129, 175, 11, 65, 30], [96, 125, 75, 118, 77]],![[0, 1], [69, 191, 182, 8, 28], [72, 0, 183, 123, 38], [88, 117, 178, 78, 59], [164, 36, 63, 50, 92], [104, 126, 187, 54], [26, 156, 96, 165, 155], [83, 128, 116, 35, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 189, 151, 129], [], [], []]
 b := ![[], [13, 115, 138, 38, 119], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : PrimeIdeal O 199 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I199N0
  hcard := NI199N0
  P := [38, 67, 153, 26, 91, 1]
  f := ofList [38, 67, 153, 26, 91, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P199P0
  hneq := by decide
  hlen := by decide
  c := ![136973790657782, 1818710939846, -13958585910608, 33662285360334, -42523022208912]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI199N0
  hpmem := by 
    show  _ ∈ I199N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI199N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := PrimeIdeal_isPrime PI199N0
def PBC199 : PrimesBelowPCertificate 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I199N
    unfold I199N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}
def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate O ℤ timesTableO I211N0
 ![![211, 0, 0, 0, 0]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 418227202051 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI211N0)

def MemCI211N0 : IdealMemCertificate O ℤ B I211N0
  ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]] ![134948304957740, 37770646433, -15205053740981, 31394161052118, -37778783533638] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI211N0
 g := ![639565426340, 179007803, -72061866071, 148787493138, -179046367458]
 hmem := by decide

def P211P0 : CertificateIrreducibleZModOfList' 211 5 2 7 [79, 44, 6, 82, 110, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [119, 63, 34, 158, 183], [136, 114, 145, 148, 20], [180, 59, 76, 106, 125], [88, 185, 167, 10, 94], [0, 1]]
 g := ![![[108, 51, 26, 6, 81], [89, 26, 90, 19, 143], [102, 153, 33, 101], [131, 193, 182, 87], [156, 40, 178, 170, 81], [101, 1], []],![[112, 119, 12, 205, 196, 47, 204, 79], [31, 79, 94, 40, 176, 118, 112, 103], [22, 75, 67, 79], [92, 128, 47, 171], [83, 169, 44, 43, 210, 60, 67, 69], [118, 153, 44, 81], [79, 77, 117, 62, 208, 127, 81, 203]],![[83, 21, 177, 175, 18, 10, 66, 188], [90, 122, 161, 52, 199, 109, 13, 114], [181, 102, 127, 76], [108, 20, 3, 62], [35, 153, 137, 181, 2, 183, 127, 203], [56, 99, 35, 209], [81, 80, 159, 86, 112, 76, 19, 193]],![[10, 111, 194, 110, 194, 175, 209, 105], [112, 91, 70, 63, 92, 82, 114, 58], [53, 139, 83, 45], [10, 18, 1, 43], [22, 28, 93, 206, 28, 26, 80, 56], [76, 184, 112, 55], [94, 209, 56, 67, 169, 175, 159, 109]],![[206, 184, 18, 150, 161, 114, 94, 149], [191, 140, 155, 194, 138, 182, 58, 15], [99, 6, 138, 45], [186, 208, 71, 99], [63, 49, 24, 82, 79, 170, 170, 132], [124, 111, 115, 25], [68, 123, 3, 189, 37, 168, 90, 88]]]
 h' := ![![[119, 63, 34, 158, 183], [143, 193, 74, 208, 202], [172, 0, 13, 4, 96], [1, 164, 185, 13, 177], [125, 148, 120, 63, 64], [39, 119, 194, 152, 202], [0, 0, 0, 1], [0, 1]],![[136, 114, 145, 148, 20], [99, 54, 151, 148, 102], [3, 111, 3, 28, 33], [105, 170, 127, 59, 76], [153, 62, 165, 130, 148], [43, 129, 118, 120, 137], [202, 41, 172, 159, 202], [119, 63, 34, 158, 183]],![[180, 59, 76, 106, 125], [198, 13, 70, 6, 145], [79, 77, 55, 151, 160], [175, 131, 182, 12, 169], [181, 149, 7, 195, 189], [189, 45, 155, 90, 57], [56, 96, 159, 77, 118], [136, 114, 145, 148, 20]],![[88, 185, 167, 10, 94], [177, 76, 88, 126, 69], [181, 48, 160, 152, 79], [88, 197, 82, 179, 195], [33, 28, 77, 189, 185], [135, 139, 8, 185, 78], [130, 62, 195, 155, 107], [180, 59, 76, 106, 125]],![[0, 1], [193, 86, 39, 145, 115], [5, 186, 191, 87, 54], [190, 182, 57, 159, 16], [89, 35, 53, 56, 47], [92, 201, 158, 86, 159], [56, 12, 107, 30, 206], [88, 185, 167, 10, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 103, 61, 4], [], [], []]
 b := ![[], [70, 71, 28, 37, 181], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : PrimeIdeal O 211 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I211N0
  hcard := NI211N0
  P := [79, 44, 6, 82, 110, 1]
  f := ofList [79, 44, 6, 82, 110, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P211P0
  hneq := by decide
  hlen := by decide
  c := ![134948304957740, 37770646433, -15205053740981, 31394161052118, -37778783533638]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI211N0
  hpmem := by 
    show  _ ∈ I211N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI211N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := PrimeIdeal_isPrime PI211N0
def PBC211 : PrimesBelowPCertificate 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I211N
    unfold I211N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}
def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6612, 2736, 1193, 1335, -3278]] i)))

def SI223N0: IdealEqSpanCertificate O ℤ timesTableO I223N0
 ![![6612, 2736, 1193, 1335, -3278]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![73, 181, 49, 1, 0], ![72, 9, 20, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![6612, 2736, 1193, 1335, -3278], ![10191, 2861, 449, -139, 1032], ![1011, -7494, -7952, -12653, 35118], ![-47316, -36139, -25529, -36411, 97854], ![-15953, -17121, -13678, -20291, 55195]]]
  hmulB := by decide
  f := ![![![-256, 215, 124, 115, -302]], ![![819, -28, 332, 423, -912]], ![![3609, -3835, -2779, -2669, 6786]], ![![1328, -785, -308, -218, 676]], ![![262, -276, -201, -192, 489]]]
  g := ![![![651, -939, 6, 1335, -3278], ![-242, 84, -60, -139, 1032], ![-7192, 8819, -405, -12653, 35118], ![-19887, 25442, -890, -36411, 97854], ![-11250, 14165, -553, -20291, 55195]]]
  hle1 := by decide
  hle2 := by decide

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI223N0)

def MemCI223N0 : IdealMemCertificate O ℤ B I223N0
  ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![73, 181, 49, 1, 0], ![72, 9, 20, 0, 1]] ![38490322, 187332703, 128142083, 178523936, -404845098] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI223N0
 g := ![72444350, -127721497, -2343627, 178523936, -404845098]
 hmem := by decide

def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [145, 116, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 87, 87], [129, 135, 136], [0, 1]]
 g := ![![[178, 85, 41], [213, 93, 218], [129, 85, 138], [137, 128, 166], [73, 132, 210], [52, 181], [1]],![[80, 195, 74, 61], [43, 208, 176, 96], [142, 4, 49, 151], [71, 43, 129, 122], [114, 149, 34, 187], [37, 121], [53, 162, 82, 207]],![[58, 126, 23, 210], [49, 48, 150, 29], [58, 31, 142, 143], [144, 37, 162, 156], [189, 158, 58, 4], [21, 202], [128, 101, 180, 16]]]
 h' := ![![[58, 87, 87], [112, 0, 189], [27, 18, 202], [205, 2, 204], [119, 142, 122], [105, 25, 136], [78, 107, 187], [0, 1]],![[129, 135, 136], [39, 37, 93], [88, 100, 69], [90, 175, 62], [38, 153, 57], [63, 20, 19], [107, 74, 212], [58, 87, 87]],![[0, 1], [135, 186, 164], [166, 105, 175], [102, 46, 180], [16, 151, 44], [116, 178, 68], [40, 42, 47], [129, 135, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 179], []]
 b := ![[], [167, 119, 203], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : PrimeIdeal O 223 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I223N0
  hcard := NI223N0
  P := [145, 116, 36, 1]
  f := ofList [145, 116, 36, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P223P0
  hneq := by decide
  hlen := by decide
  c := ![38490322, 187332703, 128142083, 178523936, -404845098]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI223N0
  hpmem := by 
    show  _ ∈ I223N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI223N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := PrimeIdeal_isPrime PI223N0
def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-256, 215, 124, 115, -302]] i)))

def SI223N1: IdealEqSpanCertificate O ℤ timesTableO I223N1
 ![![-256, 215, 124, 115, -302]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![100, 125, 1, 0, 0], ![217, 43, 0, 1, 0], ![143, 98, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-256, 215, 124, 115, -302], ![819, -28, 332, 423, -912], ![3609, -3835, -2779, -2669, 6786], ![-10248, 2233, -1657, -2791, 5352], ![-2693, -76, -1159, -1523, 3279]]]
  hmulB := by decide
  f := ![![![6612, 2736, 1193, 1335, -3278]], ![![10191, 2861, 449, -139, 1032]], ![![8682, 2797, 751, 464, -734]], ![![8187, 3052, 1133, 1109, -2552]], ![![8647, 2935, 901, 704, -1401]]]
  g := ![![![25, 42, 124, 115, -302], ![28, 133, 332, 423, -912], ![-492, -927, -2779, -2669, 6786], ![-19, -875, -1657, -2791, 5352], ![-113, -498, -1159, -1523, 3279]]]
  hle1 := by decide
  hle2 := by decide

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI223N1)

def MemCI223N1 : IdealMemCertificate O ℤ B I223N1
  ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![100, 125, 1, 0, 0], ![217, 43, 0, 1, 0], ![143, 98, 0, 0, 1]] ![309536, -13451471, -8480403, -9785216, 24653988] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI223N1
 g := ![-2483312, -4254384, -8480403, -9785216, 24653988]
 hmem := by decide

def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [42, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 222], [0, 1]]
 g := ![![[8, 8], [23, 30], [114, 55], [129, 29], [83, 135], [33], [110, 1]],![[219, 215], [201, 193], [143, 168], [197, 194], [215, 88], [33], [220, 222]]]
 h' := ![![[110, 222], [149, 30], [118, 91], [157, 72], [82, 67], [130, 71], [63, 16], [0, 1]],![[0, 1], [104, 193], [93, 132], [49, 151], [93, 156], [135, 152], [39, 207], [110, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [222, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : PrimeIdeal O 223 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I223N1
  hcard := NI223N1
  P := [42, 113, 1]
  f := ofList [42, 113, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P223P1
  hneq := by decide
  hlen := by decide
  c := ![309536, -13451471, -8480403, -9785216, 24653988]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI223N1
  hpmem := by 
    show  _ ∈ I223N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI223N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := PrimeIdeal_isPrime PI223N1
def MulI223N0 : IdealMulEqCertificate O ℤ timesTableO (I223N0) I223N1
  ![![6612, 2736, 1193, 1335, -3278]] ![![-256, 215, 124, 115, -302]]
  ![![223, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![223, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC223 : PrimesBelowPCertificate 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI223N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}
def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134041, 96103, 49395, 42034, -115706]] i)))

def SI227N0: IdealEqSpanCertificate O ℤ timesTableO I227N0
 ![![-134041, 96103, 49395, 42034, -115706]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![16, 207, 144, 68, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-134041, 96103, 49395, 42034, -115706], ![283392, 97036, 224005, 269176, -604722], ![2223474, -2007429, -1263628, -1185526, 3075354], ![-4420110, 407536, -1415266, -1920843, 4035750], ![-1024766, -289769, -749665, -904288, 2024721]]]
  hmulB := by decide
  f := ![![![-99105, -40067, -16921, -18492, 44930]], ![![-142590, -34696, -775, 10650, -38562]], ![![44064, 152309, 145646, 226540, -624762]], ![![833202, 617590, 430568, 611171, -1640130]], ![![141934, 248513, 220520, 336736, -923809]]]
  g := ![![![7565, 105935, 73617, 34846, -115706], ![43872, 551870, 384599, 182336, -604722], ![-206970, -2813241, -1956452, -926474, 3075354], ![-303930, -3678382, -2566358, -1217409, 4035750], ![-147226, -1847608, -1287707, -610508, 2024721]]]
  hle1 := by decide
  hle2 := by decide

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI227N0)

def MemCI227N0 : IdealMemCertificate O ℤ B I227N0
  ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![16, 207, 144, 68, 1]] ![-98418121211, -51238006789, -36685114067, -79270287374, 158507067138] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI227N0
 g := ![-11605864297, -144767404865, -100712347057, -47831501554, 158507067138]
 hmem := by decide

def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [36, 200, 93, 217, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 188, 42, 189], [176, 131, 70, 133], [198, 134, 115, 132], [0, 1]]
 g := ![![[111, 200, 39, 26], [130, 77, 214, 40], [117, 68, 82], [220, 31, 89], [157, 41, 113], [75, 7, 10, 1], []],![[183, 22, 209, 152, 166, 188], [136, 110, 5, 123, 57, 76], [100, 0, 113], [143, 183, 177], [155, 207, 213], [185, 211, 114, 164, 133, 49], [205, 31, 164, 208, 56, 62]],![[50, 195, 113, 178, 73, 59], [148, 177, 132, 214, 184, 69], [161, 197, 222], [84, 106, 4], [186, 138, 84], [160, 216, 8, 4, 60, 97], [169, 215, 41, 80, 152, 9]],![[187, 128, 111, 102, 170, 69], [138, 26, 124, 53, 91, 176], [52, 147, 175], [222, 202, 144], [138, 40, 34], [6, 192, 51, 138, 29, 133], [182, 149, 156, 169, 133, 4]]]
 h' := ![![[90, 188, 42, 189], [87, 64, 80, 88], [190, 8, 111, 128], [166, 56, 213, 189], [145, 18, 166, 61], [24, 184, 118, 106], [0, 0, 0, 1], [0, 1]],![[176, 131, 70, 133], [202, 106, 101, 190], [18, 93, 33, 15], [126, 41, 151, 106], [196, 197, 115, 152], [151, 25, 86, 101], [214, 131, 192, 29], [90, 188, 42, 189]],![[198, 134, 115, 132], [9, 4, 73, 180], [91, 87, 46, 193], [165, 87, 52, 201], [187, 164, 130, 2], [46, 16, 105, 68], [189, 13, 86, 117], [176, 131, 70, 133]],![[0, 1], [48, 53, 200, 223], [151, 39, 37, 118], [175, 43, 38, 185], [201, 75, 43, 12], [185, 2, 145, 179], [158, 83, 176, 80], [198, 134, 115, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [164, 112, 96], []]
 b := ![[], [], [138, 117, 221, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : PrimeIdeal O 227 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I227N0
  hcard := NI227N0
  P := [36, 200, 93, 217, 1]
  f := ofList [36, 200, 93, 217, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P227P0
  hneq := by decide
  hlen := by decide
  c := ![-98418121211, -51238006789, -36685114067, -79270287374, 158507067138]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI227N0
  hpmem := by 
    show  _ ∈ I227N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI227N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := PrimeIdeal_isPrime PI227N0
def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99105, 40067, 16921, 18492, -44930]] i)))

def SI227N1: IdealEqSpanCertificate O ℤ timesTableO I227N1
 ![![99105, 40067, 16921, 18492, -44930]] 
 ![![227, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![178, 0, 1, 0, 0], ![168, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![99105, 40067, 16921, 18492, -44930], ![142590, 34696, 775, -10650, 38562], ![-44064, -152309, -145646, -226540, 624762], ![-833202, -617590, -430568, -611171, 1640130], ![-317876, -306979, -237553, -349006, 946621]]]
  hmulB := by decide
  f := ![![![134041, -96103, -49395, -42034, 115706]], ![![2885, -3391, -2510, -2482, 6232]], ![![95312, -66515, -33166, -27738, 77182]], ![![118674, -72920, -30322, -22647, 67854]], ![![78916, -52067, -24115, -19348, 55305]]]
  g := ![![![-2814, 40067, 16921, 18492, -44930], ![-14572, 34696, 775, -10650, 38562], ![-60415, -152309, -145646, -226540, 624762], ![-105060, -617590, -430568, -611171, 1640130], ![-72801, -306979, -237553, -349006, 946621]]]
  hle1 := by decide
  hle2 := by decide

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulEqCertificate O ℤ timesTableO (I227N0) I227N1
  ![![-134041, 96103, 49395, 42034, -115706]] ![![99105, 40067, 16921, 18492, -44930]]
  ![![227, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC227 : PrimesBelowPCertificate 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI227N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}
def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate O ℤ timesTableO I229N0
 ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 629763392149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI229N0)

def MemCI229N0 : IdealMemCertificate O ℤ B I229N0
  ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] ![139321491219837, 3893418738179, -12506761247573, 36300379912192, -48043293828222] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI229N0
 g := ![608390791353, 17001828551, -54614677937, 158516942848, -209796042918]
 hmem := by decide

def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [196, 124, 67, 24, 69, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 168, 95, 37, 74], [19, 50, 197, 22, 16], [207, 0, 116, 73, 222], [224, 10, 50, 97, 146], [0, 1]]
 g := ![![[130, 69, 106, 52, 147], [110, 67, 11, 76], [158, 50, 42, 54, 42], [60, 164, 191, 181], [182, 35, 155, 186], [157, 160, 1], []],![[78, 5, 159, 96, 222, 72, 77, 63], [175, 72, 83, 148], [191, 20, 122, 212, 148, 155, 163, 32], [17, 217, 204, 146], [152, 81, 45, 214], [64, 163, 78, 131, 119, 117, 170, 205], [221, 37, 167, 117, 18, 114, 56, 123]],![[109, 123, 14, 12, 151, 81, 228, 147], [4, 185, 192, 210], [171, 103, 94, 134, 99, 46, 118, 15], [84, 142, 187, 27], [136, 196, 68, 153], [75, 167, 209, 84, 56, 184, 176, 55], [210, 146, 142, 121, 63, 85, 141, 203]],![[104, 133, 207, 78, 205, 165, 81, 101], [61, 11, 65, 174], [24, 199, 201, 113, 198, 73, 58, 188], [217, 175, 68, 224], [6, 52, 116, 118], [89, 16, 32, 9, 206, 129, 166, 131], [142, 188, 60, 151, 212, 60, 48, 115]],![[180, 34, 117, 37, 4, 55, 193, 121], [143, 98, 228, 58], [205, 164, 225, 62, 142, 160, 156, 56], [130, 115, 166, 187], [192, 18, 99, 149], [59, 223, 133, 55, 64, 72, 204, 126], [215, 146, 74, 135, 155, 133, 71, 26]]]
 h' := ![![[168, 168, 95, 37, 74], [27, 15, 25, 163, 39], [176, 134, 29, 11, 166], [121, 218, 47, 98, 202], [120, 225, 41, 218, 69], [143, 10, 131, 44, 145], [0, 0, 0, 1], [0, 1]],![[19, 50, 197, 22, 16], [39, 4, 179, 214, 120], [26, 37, 75, 34, 47], [45, 157, 121, 227, 146], [20, 15, 78, 100, 72], [202, 14, 41, 129, 108], [152, 26, 174, 176, 57], [168, 168, 95, 37, 74]],![[207, 0, 116, 73, 222], [190, 148, 77, 127, 67], [79, 164, 153, 14, 50], [75, 196, 167, 121, 141], [153, 187, 73, 122, 213], [4, 92, 71, 139, 100], [49, 181, 206, 48, 126], [19, 50, 197, 22, 16]],![[224, 10, 50, 97, 146], [101, 34, 70, 75, 76], [81, 80, 134, 207, 116], [144, 228, 228, 154, 44], [178, 170, 206, 143, 192], [155, 188, 217, 48, 24], [221, 46, 186, 57, 48], [207, 0, 116, 73, 222]],![[0, 1], [172, 28, 107, 108, 156], [105, 43, 67, 192, 79], [88, 117, 124, 87, 154], [148, 90, 60, 104, 141], [37, 154, 227, 98, 81], [100, 205, 121, 176, 227], [224, 10, 50, 97, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 64, 189, 224], [], [], []]
 b := ![[], [115, 195, 142, 16, 96], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : PrimeIdeal O 229 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I229N0
  hcard := NI229N0
  P := [196, 124, 67, 24, 69, 1]
  f := ofList [196, 124, 67, 24, 69, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P229P0
  hneq := by decide
  hlen := by decide
  c := ![139321491219837, 3893418738179, -12506761247573, 36300379912192, -48043293828222]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI229N0
  hpmem := by 
    show  _ ∈ I229N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI229N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := PrimeIdeal_isPrime PI229N0
def PBC229 : PrimesBelowPCertificate 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I229N
    unfold I229N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}
def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21477, -11477, -6537, -8544, 22304]] i)))

def SI233N0: IdealEqSpanCertificate O ℤ timesTableO I233N0
 ![![-21477, -11477, -6537, -8544, 22304]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![10, 67, 56, 1, 0], ![60, 158, 195, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-21477, -11477, -6537, -8544, 22304], ![-61248, -32142, -18037, -23410, 60960], ![-168270, -86505, -47692, -61364, 159300], ![-190656, -94720, -50672, -64205, 165738], ![-167092, -84739, -46177, -59068, 153011]]]
  hmulB := by decide
  f := ![![![-5395, 6579, 1629, 2974, -6752]], ![![24354, -29642, -7323, -13376, 30372]], ![![-109524, 133307, 32822, 60090, -136404]], ![![-18548, 22574, 5551, 10171, -23086]], ![![-76258, 92820, 22839, 41832, -94953]]]
  g := ![![![-5469, -12717, -16641, -8544, 22304], ![-14956, -34744, -45469, -23410, 60960], ![-39110, -90749, -118776, -61364, 159300], ![-40742, -94333, -123494, -64205, 165738], ![-37584, -87137, -114058, -59068, 153011]]]
  hle1 := by decide
  hle2 := by decide

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI233N0)

def MemCI233N0 : IdealMemCertificate O ℤ B I233N0
  ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![10, 67, 56, 1, 0], ![60, 158, 195, 0, 1]] ![38553798, 184772967, 126553035, 176506592, -400008378] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI233N0
 g := ![95596526, 221288219, 292891921, 176506592, -400008378]
 hmem := by decide

def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [37, 44, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 81, 122], [229, 151, 111], [0, 1]]
 g := ![![[190, 65, 217], [50, 205], [231, 196], [8, 172, 62], [97, 56], [173, 5, 72], [1]],![[30, 227, 49, 90], [135, 217], [133, 46], [111, 175, 42, 111], [167, 102], [106, 104, 163, 73], [160, 212, 205, 79]],![[178, 105, 128, 61], [52, 144], [108, 141], [151, 101, 9, 134], [201, 50], [65, 161, 125, 5], [111, 11, 112, 154]]]
 h' := ![![[193, 81, 122], [214, 85, 110], [82, 171, 111], [170, 25, 14], [123, 34, 166], [123, 96, 216], [196, 189, 189], [0, 1]],![[229, 151, 111], [123, 78, 185], [218, 223, 110], [180, 197, 38], [54, 52, 89], [116, 10, 58], [213, 184, 104], [193, 81, 122]],![[0, 1], [164, 70, 171], [199, 72, 12], [1, 11, 181], [1, 147, 211], [139, 127, 192], [23, 93, 173], [229, 151, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 105], []]
 b := ![[], [122, 226, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : PrimeIdeal O 233 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I233N0
  hcard := NI233N0
  P := [37, 44, 44, 1]
  f := ofList [37, 44, 44, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P233P0
  hneq := by decide
  hlen := by decide
  c := ![38553798, 184772967, 126553035, 176506592, -400008378]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI233N0
  hpmem := by 
    show  _ ∈ I233N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI233N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := PrimeIdeal_isPrime PI233N0
def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5395, 6579, 1629, 2974, -6752]] i)))

def SI233N1: IdealEqSpanCertificate O ℤ timesTableO I233N1
 ![![-5395, 6579, 1629, 2974, -6752]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![62, 121, 1, 0, 0], ![210, 167, 0, 1, 0], ![184, 79, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-5395, 6579, 1629, 2974, -6752], ![24354, -29642, -7323, -13376, 30372], ![-109524, 133307, 32822, 60090, -136404], ![233892, -285226, -70298, -128745, 292182], ![64834, -79109, -19509, -35726, 81075]]]
  hmulB := by decide
  f := ![![![-21477, -11477, -6537, -8544, 22304]], ![![-61248, -32142, -18037, -23410, 60960]], ![![-38244, -20117, -11311, -14694, 38276]], ![![-64074, -33788, -19037, -24755, 64506]], ![![-38444, -20325, -11476, -14938, 38939]]]
  g := ![![![2195, -660, 1629, 2974, -6752], ![-9876, 2965, -7323, -13376, 30372], ![44356, -13293, 32822, 60090, -136404], ![-94990, 28493, -70298, -128745, 292182], ![-26356, 7909, -19509, -35726, 81075]]]
  hle1 := by decide
  hle2 := by decide

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI233N1)

def MemCI233N1 : IdealMemCertificate O ℤ B I233N1
  ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![62, 121, 1, 0, 0], ![210, 167, 0, 1, 0], ![184, 79, 0, 0, 1]] ![292225, -13371875, -8433510, -9728357, 24508161] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI233N1
 g := ![-8340673, 2985295, -8433510, -9728357, 24508161]
 hmem := by decide

def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [89, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 232], [0, 1]]
 g := ![![[54, 144], [175], [62], [94, 132], [16], [221, 110], [87, 1]],![[0, 89], [175], [62], [161, 101], [16], [5, 123], [174, 232]]]
 h' := ![![[87, 232], [112, 221], [92, 116], [22, 166], [63, 150], [136, 4], [179, 24], [0, 1]],![[0, 1], [0, 12], [165, 117], [18, 67], [65, 83], [18, 229], [170, 209], [87, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [201, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : PrimeIdeal O 233 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I233N1
  hcard := NI233N1
  P := [89, 146, 1]
  f := ofList [89, 146, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P233P1
  hneq := by decide
  hlen := by decide
  c := ![292225, -13371875, -8433510, -9728357, 24508161]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI233N1
  hpmem := by 
    show  _ ∈ I233N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI233N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := PrimeIdeal_isPrime PI233N1
def MulI233N0 : IdealMulEqCertificate O ℤ timesTableO (I233N0) I233N1
  ![![-21477, -11477, -6537, -8544, 22304]] ![![-5395, 6579, 1629, 2974, -6752]]
  ![![233, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![233, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC233 : PrimesBelowPCertificate 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI233N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}
def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![51, 33, -4, -5, 13]] i)))

def SI239N0: IdealEqSpanCertificate O ℤ timesTableO I239N0
 ![![239, 0, 0, 0, 0], ![51, 33, -4, -5, 13]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![125, 217, 1, 0, 0], ![180, 60, 0, 1, 0], ![130, 74, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![0, 0, 0, 0, 239]], ![![51, 33, -4, -5, 13], ![-36, 46, 30, -13, 33], ![-96, 13, 51, 63, 45], ![558, -2858, -1660, -1999, 5100], ![52, -1122, -658, -822, 2161]]]
  hmulB := by decide
  f := ![![![3754517308, -4786751429, -3124751438, 1352337560, -3435438484], ![-22618243, 24885661095, 3044860, 0, 0]], ![![574670499, -732665398, -478277860, 206990262, -525831962], ![-3461915, 3809026411, 466050, 0, 0]], ![![2485271341, -3168550107, -2068403097, 895168546, -2274059794], ![-14971906, 16472855368, 2015520, 0, 0]], ![![2971938690, -3789017490, -2473439040, 1070460989, -2719367550], ![-17903790, 19698579840, 2410200, 0, 0]], ![![2220137495, -2830522715, -1847741624, 799670137, -2031458450], ![-13374589, 14715497476, 1800500, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-125, -217, 239, 0, 0], ![-180, -60, 0, 239, 0], ![-130, -74, 0, 0, 239]], ![![-1, 1, -4, -5, 13], ![-24, -34, 30, -13, 33], ![-99, -76, 51, 63, 45], ![-398, 418, -1660, -1999, 5100], ![-212, 130, -658, -822, 2161]]]
  hle1 := by decide
  hle2 := by decide

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI239N0)

def MemCI239N0 : IdealMemCertificate O ℤ B I239N0
  ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![125, 217, 1, 0, 0], ![180, 60, 0, 1, 0], ![130, 74, 0, 0, 1]] ![2965, -295872, -184662, -234722, 561036] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI239N0
 g := ![-31795, 51642, -184662, -234722, 561036]
 hmem := by decide

def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [202, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 238], [0, 1]]
 g := ![![[173, 155], [208, 4], [132, 49], [67, 71], [153], [123, 116], [187, 1]],![[0, 84], [0, 235], [213, 190], [199, 168], [153], [66, 123], [135, 238]]]
 h' := ![![[187, 238], [48, 148], [104, 2], [89, 7], [25, 166], [10, 191], [227, 112], [0, 1]],![[0, 1], [0, 91], [0, 237], [203, 232], [236, 73], [116, 48], [139, 127], [187, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [63, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : PrimeIdeal O 239 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I239N0
  hcard := NI239N0
  P := [202, 52, 1]
  f := ofList [202, 52, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P239P0
  hneq := by decide
  hlen := by decide
  c := ![2965, -295872, -184662, -234722, 561036]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI239N0
  hpmem := by 
    show  _ ∈ I239N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI239N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := PrimeIdeal_isPrime PI239N0
def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![-41, 50, -4, -5, 13]] i)))

def SI239N1: IdealEqSpanCertificate O ℤ timesTableO I239N1
 ![![239, 0, 0, 0, 0], ![-41, 50, -4, -5, 13]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![197, 224, 1, 0, 0], ![163, 106, 0, 1, 0], ![65, 40, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![0, 0, 0, 0, 239]], ![![-41, 50, -4, -5, 13], ![-36, -46, 47, -13, 33], ![-96, 30, -41, 97, 45], ![813, -4048, -2357, -2958, 7242], ![103, -1581, -930, -1162, 2936]]]
  hmulB := by decide
  f := ![![![462208147981, 579631526916, -597274580846, 165855917158, -421057345110], ![25594625676, 3039387006594, 4536220, 0, 0]], ![![650646496516, 815942392811, -840778370465, 233473970319, -592718859719], ![36029337952, 4278519355375, 6385602, 0, 0]], ![![990779351152, 1242485556870, -1280304824241, 355525143169, -902569383525], ![54864083979, 6515164000066, 9723746, 0, 0]], ![![603801074293, 757195951966, -780243782204, 216664248331, -550044127132], ![33435288008, 3970473362948, 5925848, 0, 0]], ![![234599955977, 294199769720, -303154738802, 84182399280, -213713313057], ![12990896158, 1542681713990, 2302420, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-197, -224, 239, 0, 0], ![-163, -106, 0, 239, 0], ![-65, -40, 0, 0, 239]], ![![3, 4, -4, -5, 13], ![-39, -44, 47, -13, 33], ![-45, -12, -41, 97, 45], ![1994, 2292, -2357, -2958, 7242], ![761, 889, -930, -1162, 2936]]]
  hle1 := by decide
  hle2 := by decide

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI239N1)

def MemCI239N1 : IdealMemCertificate O ℤ B I239N1
  ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![197, 224, 1, 0, 0], ![163, 106, 0, 1, 0], ![65, 40, 0, 0, 1]] ![331294, -13550363, -8538664, -9855859, 24835167] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI239N1
 g := ![7006976, 8160773, -8538664, -9855859, 24835167]
 hmem := by decide

def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [234, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 238], [0, 1]]
 g := ![![[129, 67], [80, 147], [209, 31], [2, 225], [99], [141, 220], [167, 1]],![[85, 172], [12, 92], [128, 208], [54, 14], [99], [75, 19], [95, 238]]]
 h' := ![![[167, 238], [161, 28], [89, 25], [10, 134], [161, 224], [227, 92], [118, 170], [0, 1]],![[0, 1], [57, 211], [201, 214], [161, 105], [46, 15], [56, 147], [67, 69], [167, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [81, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : PrimeIdeal O 239 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I239N1
  hcard := NI239N1
  P := [234, 72, 1]
  f := ofList [234, 72, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P239P1
  hneq := by decide
  hlen := by decide
  c := ![331294, -13550363, -8538664, -9855859, 24835167]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI239N1
  hpmem := by 
    show  _ ∈ I239N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI239N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := PrimeIdeal_isPrime PI239N1
def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0], ![37, 1, 0, 0, 0]] i)))

def SI239N2: IdealEqSpanCertificate O ℤ timesTableO I239N2
 ![![239, 0, 0, 0, 0], ![37, 1, 0, 0, 0]] 
 ![![239, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![213, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![0, 0, 0, 0, 239]], ![![37, 1, 0, 0, 0], ![0, 37, 1, 0, 0], ![0, 1, 37, 2, 0], ![15, -70, -41, -14, 126], ![3, -27, -16, -20, 88]]]
  hmulB := by decide
  f := ![![![-132908965516, -35364180200, -1233322212455, -66667808634, -5714730], ![858515680024, -10070184696, 7966879010678, 10839845, 0]], ![![-20659424899, -5497022908, -191708117769, -10362871908, -888300], ![133448034504, -1565313531, 1238374987656, 1684950, 0]], ![![-36498316784, -9711406977, -338684336123, -18307740086, -1569330], ![235758190818, -2765387261, 2187795777492, 2976745, 0]], ![![-118447368263, -31516264246, -1099126531324, -59413798369, -5092920], ![765102057010, -8974464956, 7100016527756, 9660380, 0]], ![![-556104496, -147967313, -5160343986, -278944806, -23911], ![3592116060, -42134465, 33334221802, 45355, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-37, 239, 0, 0, 0], ![-65, 0, 239, 0, 0], ![-213, 0, 0, 239, 0], ![-1, 0, 0, 0, 239]], ![![0, 1, 0, 0, 0], ![-6, 37, 1, 0, 0], ![-12, 1, 37, 2, 0], ![34, -70, -41, -14, 126], ![26, -27, -16, -20, 88]]]
  hle1 := by decide
  hle2 := by decide

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulEqCertificate O ℤ timesTableO (I239N0) I239N1
  ![![239, 0, 0, 0, 0], ![51, 33, -4, -5, 13]] ![![239, 0, 0, 0, 0], ![-41, 50, -4, -5, 13]]
  ![![239, 0, 0, 0, 0], ![1148, 653, 407, 507, -1318]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![57121, 0, 0, 0, 0], ![-9799, 11950, -956, -1195, 3107]], ![![12189, 7887, -956, -1195, 3107], ![-5621, 599, 1206, -1388, 3530]]]
 hmul := by decide
 f :=  ![![![![-8007753817592345756940472634647, -10042113261787644215314408140998, 10347779081480789296256956735832, -2873452922875424356043740395122, 7294816366789652543301186007222], ![-443426759461826724155040735772, -52657364461766928401254701034600, -78590031466371896004446112, 0, 0]], ![![108743772141950616, -3856982959890, 0, 0, 0], ![25334, 0, 0, 0, 0]]], ![![![-38464141953167467607089619987957, -48235907198171198643428038272523, 49704130840746089800683508704060, -13802235138449261624010730840641, 35039645154682078636897865106714], ![-2129939332588137192818977524419, -252932393736606244600542591979817, -377496386038414379464598192, 0, 0]], ![![522335724033095992, -18526486135752, 0, 0, 0], ![121688, 0, 0, 0, 0]]]]
 g :=  ![![![![-909, -653, -407, -507, 1318], ![239, 0, 0, 0, 0]], ![![-41, 50, -4, -5, 13], ![0, 0, 0, 0, 0]]], ![![![-1097, -620, -411, -512, 1331], ![239, 0, 0, 0, 0]], ![![-427, -227, -138, -184, 478], ![84, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI239N1 : IdealMulEqCertificate O ℤ timesTableO (I239N0*I239N1) I239N2
  ![![239, 0, 0, 0, 0], ![1148, 653, 407, 507, -1318]] ![![239, 0, 0, 0, 0], ![37, 1, 0, 0, 0]]
  ![![239, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI239N0
 hI2 := rfl
 M :=  ![![![57121, 0, 0, 0, 0], ![8843, 239, 0, 0, 0]], ![![274372, 156067, 97273, 121173, -315002], ![46127, 25812, 16013, 20076, -52102]]]
 hmul := by decide
 f :=  ![![![![-2692614599446587252, -725678334286658276, -25342982594982831297, -1369937759375399676, -366323472606], ![17392834563377281450, -207114355096520250, 163707567109321932900, 694851665853, 0]], ![![-42, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![239, 0, 0, 0, 0]], ![![37, 1, 0, 0, 0]]], ![![![1148, 653, 407, 507, -1318]], ![![193, 108, 67, 84, -218]]]]
 hle1 := by decide
 hle2 := by decide

def PBC239 : PrimesBelowPCertificate 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI239N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}
def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![17, -79, -4, -5, 13]] i)))

def SI241N0: IdealEqSpanCertificate O ℤ timesTableO I241N0
 ![![241, 0, 0, 0, 0], ![17, -79, -4, -5, 13]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![180, 189, 1, 0, 0], ![101, 64, 0, 1, 0], ![77, 225, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]], ![![17, -79, -4, -5, 13], ![-36, 12, -82, -13, 33], ![-96, -99, 17, -161, 45], ![-1122, 4982, 2932, 3679, -9012], ![-284, 1902, 1134, 1418, -3585]]]
  hmulB := by decide
  f := ![![![840887901036, -260687302261, 1926775892948, 306633566425, -778455802625], ![64436491253, 5659698647232, 2637504, 0, 0]], ![![1905134824557, -590619103073, 4365347447889, 694716007986, -1763687237166], ![145988785395, 12822742455912, 5975595, 0, 0]], ![![2122062926011, -657869923904, 4862407562393, 773819818757, -1964509414669], ![162611792617, 14282803518516, 6656004, 0, 0]], ![![858333223141, -266095602192, 1966749385280, 312995081825, -794605888976], ![65773310672, 5777116516800, 2692224, 0, 0]], ![![2047318273470, -634698010253, 4691140744945, 746563844030, -1895314212297], ![156884176447, 13779725512104, 6421563, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-180, -189, 241, 0, 0], ![-101, -64, 0, 241, 0], ![-77, -225, 0, 0, 241]], ![![1, -8, -4, -5, 13], ![56, 37, -82, -13, 33], ![40, -13, 17, -161, 45], ![-857, 5158, 2932, 3679, -9012], ![-297, 2089, 1134, 1418, -3585]]]
  hle1 := by decide
  hle2 := by decide

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI241N0)

def MemCI241N0 : IdealMemCertificate O ℤ B I241N0
  ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![180, 189, 1, 0, 0], ![101, 64, 0, 1, 0], ![77, 225, 0, 0, 1]] ![7287, -316412, -196570, -249594, 598164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI241N0
 g := ![60333, -339326, -196570, -249594, 598164]
 hmem := by decide

def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [104, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 240], [0, 1]]
 g := ![![[], [], [], [182], [0, 193], [0, 212], [0, 1]],![[], [], [], [182], [0, 48], [0, 29], [0, 240]]]
 h' := ![![[0, 240], [177], [30], [111], [0, 172], [0, 124], [0, 137], [0, 1]],![[0, 1], [177], [30], [111], [0, 69], [0, 117], [0, 104], [0, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [0, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : PrimeIdeal O 241 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I241N0
  hcard := NI241N0
  P := [104, 0, 1]
  f := ofList [104, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P241P0
  hneq := by decide
  hlen := by decide
  c := ![7287, -316412, -196570, -249594, 598164]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI241N0
  hpmem := by 
    show  _ ∈ I241N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI241N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := PrimeIdeal_isPrime PI241N0
def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![-116, 93, -4, -5, 13]] i)))

def SI241N1: IdealEqSpanCertificate O ℤ timesTableO I241N1
 ![![241, 0, 0, 0, 0], ![-116, 93, -4, -5, 13]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![64, 38, 1, 0, 0], ![230, 154, 0, 1, 0], ![229, 41, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]], ![![-116, 93, -4, -5, 13], ![-36, -121, 90, -13, 33], ![-96, 73, -116, 183, 45], ![1458, -7058, -4120, -5226, 12660], ![232, -2742, -1618, -2022, 5054]]]
  hmulB := by decide
  f := ![![![219739627273, 539435327450, -428108594188, 64137186762, -162939316386], ![99382680588, 1150798303254, 1253200, 0, 0]], ![![199962658960, 490885161333, -389578037708, 58364722648, -148274479904], ![90438057650, 1047224351178, 1140412, 0, 0]], ![![89874356060, 220631131667, -175098067979, 26232357027, -66642809531], ![40647900239, 470680949348, 512564, 0, 0]], ![![337486986498, 828491452963, -657510350500, 98505063248, -250250260055], ![152636835683, 1767452945352, 1924728, 0, 0]], ![![242816778765, 596087060519, -473068745288, 70872902066, -180051274401], ![109819893190, 1271655642504, 1384812, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-64, -38, 241, 0, 0], ![-230, -154, 0, 241, 0], ![-229, -41, 0, 0, 241]], ![![-7, 2, -4, -5, 13], ![-43, -12, 90, -13, 33], ![-187, -106, -116, 183, 45], ![-5942, 1806, -4120, -5226, 12660], ![-2442, 676, -1618, -2022, 5054]]]
  hle1 := by decide
  hle2 := by decide

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI241N1)

def MemCI241N1 : IdealMemCertificate O ℤ B I241N1
  ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![64, 38, 1, 0, 0], ![230, 154, 0, 1, 0], ![229, 41, 0, 0, 1]] ![310630, -13456295, -8483245, -9788662, 24662826] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI241N1
 g := ![-11838824, 3341017, -8483245, -9788662, 24662826]
 hmem := by decide

def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [84, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [130, 240], [0, 1]]
 g := ![![[96, 192], [239], [83], [67], [14, 229], [134, 24], [130, 1]],![[233, 49], [239], [83], [67], [141, 12], [121, 217], [19, 240]]]
 h' := ![![[130, 240], [88, 34], [142, 203], [33, 223], [29, 157], [71, 62], [166, 187], [0, 1]],![[0, 1], [170, 207], [22, 38], [103, 18], [195, 84], [178, 179], [135, 54], [130, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [239, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : PrimeIdeal O 241 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I241N1
  hcard := NI241N1
  P := [84, 111, 1]
  f := ofList [84, 111, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P241P1
  hneq := by decide
  hlen := by decide
  c := ![310630, -13456295, -8483245, -9788662, 24662826]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI241N1
  hpmem := by 
    show  _ ∈ I241N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI241N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := PrimeIdeal_isPrime PI241N1
def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def SI241N2: IdealEqSpanCertificate O ℤ timesTableO I241N2
 ![![241, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]], ![![14, 1, 0, 0, 0], ![0, 14, 1, 0, 0], ![0, 1, 14, 2, 0], ![15, -70, -41, -37, 126], ![3, -27, -16, -20, 65]]]
  hmulB := by decide
  f := ![![![-35482383068, -35680751233, -467194473500, -66743626187, -2953818], ![610797826656, -3860912303, 8042711476149, 5649763, 0]], ![![-2087199121, -2098867821, -27482029064, -3926095831, -173754], ![35929285935, -227112375, 473100695907, 332339, 0]], ![![-6857939544, -6896279582, -90298090497, -12900028445, -570906], ![118053360756, -746226615, 1554473629086, 1091971, 0]], ![![-23555531615, -23687221411, -310154314346, -44308793856, -1960938], ![405487632795, -2563126587, 5339279047284, 3750683, 0]], ![![-11925614240, -11992285689, -157023868687, -22432505067, -992777], ![205288896334, -1297650956, 2703151989909, 1898883, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-14, 241, 0, 0, 0], ![-45, 0, 241, 0, 0], ![-160, 0, 0, 241, 0], ![-81, 0, 0, 0, 241]], ![![0, 1, 0, 0, 0], ![-1, 14, 1, 0, 0], ![-4, 1, 14, 2, 0], ![-6, -70, -41, -37, 126], ![-4, -27, -16, -20, 65]]]
  hle1 := by decide
  hle2 := by decide

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulEqCertificate O ℤ timesTableO (I241N0) I241N1
  ![![241, 0, 0, 0, 0], ![17, -79, -4, -5, 13]] ![![241, 0, 0, 0, 0], ![-116, 93, -4, -5, 13]]
  ![![241, 0, 0, 0, 0], ![1523, 845, 539, 690, -1801]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![58081, 0, 0, 0, 0], ![-27956, 22413, -964, -1205, 3133]], ![![4097, -19039, -964, -1205, 3133], ![-3018, 10492, -7148, 54, -164]]]
 hmul := by decide
 f :=  ![![![![355878437346700153820033043078, 873640334105298285559541403888, -693341567049512052218518245264, 103873125131795041825396658902, -263887720292162315875878519928], ![160954824142392056461718616453, 1863770804349974769848374085802, 2029620407689592365923444, 0, 0]], ![![7115979017255849225, 6915371027112, 0, 0, 0], ![47477, 0, 0, 0, 0]]], ![![![2248975943614361040191938867469, 5520975390986967384554738585747, -4381576238863674074416081634657, 656426844377390773913938054946, -1667640049161329919598105548519], ![1017154987539388131015124663970, 11778110903950070787730458044088, 12826198478318651719665424, 0, 0]], ![![44969472565942633940, 43701729155316, 0, 0, 0], ![300031, 0, 0, 0, 0]]]]
 g :=  ![![![![-1282, -845, -539, -690, 1801], ![241, 0, 0, 0, 0]], ![![-116, 93, -4, -5, 13], ![0, 0, 0, 0, 0]]], ![![![17, -79, -4, -5, 13], ![0, 0, 0, 0, 0]], ![![-556, -258, -222, -246, 642], ![86, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI241N1 : IdealMulEqCertificate O ℤ timesTableO (I241N0*I241N1) I241N2
  ![![241, 0, 0, 0, 0], ![1523, 845, 539, 690, -1801]] ![![241, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  ![![241, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI241N0
 hI2 := rfl
 M :=  ![![![58081, 0, 0, 0, 0], ![3374, 241, 0, 0, 0]], ![![367043, 203645, 129899, 166290, -434041], ![26269, 14219, 8917, 11568, -30125]]]
 hmul := by decide
 f :=  ![![![![-96421422465319534295312, -7132744135769474137263, -3460134144540871887381, -494321815211836718107, -55458091367758], ![1659825915182206337558032, -28596552281951781042, 59565780695406486635649, 106074603243203, 0]], ![![-6100, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![241, 0, 0, 0, 0]], ![![14, 1, 0, 0, 0]]], ![![![1523, 845, 539, 690, -1801]], ![![109, 59, 37, 48, -125]]]]
 hle1 := by decide
 hle2 := by decide

def PBC241 : PrimesBelowPCertificate 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI241N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}
def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![-433, -295, -114, -143, 372]] i)))

def SI251N0: IdealEqSpanCertificate O ℤ timesTableO I251N0
 ![![251, 0, 0, 0, 0], ![-433, -295, -114, -143, 372]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![43, 220, 83, 1, 0], ![180, 214, 93, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]], ![![-433, -295, -114, -143, 372], ![-1029, -581, -384, -375, 954], ![-2763, -921, -470, -723, 1404], ![-2802, 5025, 3321, 4114, -10224], ![-2307, 1356, 991, 1249, -3220]]]
  hmulB := by decide
  f := ![![![23014, -7011, 27432, 14247, -32994], ![-99396, 47439, 0, 0, 0]], ![![-7238, 2633, -9030, -4606, 10626], ![33383, -15813, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-2379, 1122, -3209, -1589, 3642], ![12245, -5733, 0, 0, 0]], ![![9988, -3018, 11883, 6176, -14305], ![-43018, 20538, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-43, -220, -83, 251, 0], ![-180, -214, -93, 0, 251]], ![![-244, -193, -91, -143, 372], ![-624, -487, -231, -375, 954], ![-894, -567, -283, -723, 1404], ![6616, 5131, 2441, 4114, -10224], ![2086, 1656, 784, 1249, -3220]]]
  hle1 := by decide
  hle2 := by decide

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI251N0)

def MemCI251N0 : IdealMemCertificate O ℤ B I251N0
  ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![43, 220, 83, 1, 0], ![180, 214, 93, 0, 1]] ![38378583, 192380285, 131278501, 182506572, -414388590] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI251N0
 g := ![266057937, 194103955, 93710645, 182506572, -414388590]
 hmem := by decide

def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [104, 78, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 26, 218], [225, 224, 33], [0, 1]]
 g := ![![[82, 160, 180], [60, 88, 119], [119, 156], [192, 151, 205], [75, 140, 3], [89, 140, 149], [1]],![[67, 171, 194, 38], [180, 39, 77, 25], [248, 147], [93, 9], [78, 13, 143, 197], [124, 103, 126, 36], [188, 184, 231, 207]],![[216, 90, 49, 70], [33, 59, 5, 230], [107, 201], [122, 63, 109, 239], [198, 236, 211, 146], [165, 147, 100, 8], [181, 43, 16, 44]]]
 h' := ![![[6, 26, 218], [35, 85, 155], [168, 198, 133], [112, 52, 77], [232, 129, 177], [31, 107, 76], [147, 173, 231], [0, 1]],![[225, 224, 33], [135, 28, 38], [235, 71, 166], [26, 64, 221], [52, 51], [140, 96, 190], [242, 132, 102], [6, 26, 218]],![[0, 1], [162, 138, 58], [230, 233, 203], [125, 135, 204], [107, 71, 74], [11, 48, 236], [246, 197, 169], [225, 224, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 108], []]
 b := ![[], [217, 137, 163], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : PrimeIdeal O 251 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I251N0
  hcard := NI251N0
  P := [104, 78, 20, 1]
  f := ofList [104, 78, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P251P0
  hneq := by decide
  hlen := by decide
  c := ![38378583, 192380285, 131278501, 182506572, -414388590]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI251N0
  hpmem := by 
    show  _ ∈ I251N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI251N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := PrimeIdeal_isPrime PI251N0
def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![93, 1, 0, 0, 0]] i)))

def SI251N1: IdealEqSpanCertificate O ℤ timesTableO I251N1
 ![![251, 0, 0, 0, 0], ![93, 1, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]], ![![93, 1, 0, 0, 0], ![0, 93, 1, 0, 0], ![0, 1, 93, 2, 0], ![15, -70, -41, 42, 126], ![3, -27, -16, -20, 144]]]
  hmulB := by decide
  f := ![![![11276432686, 1454630817, 163456627024, 3515076288, -641088], ![-30434449035, 1146025840, -441168892992, 1277088, 0]], ![![4184336676, 539768645, 60653718981, 1304336528, -237888], ![-11293286171, 425254993, -163704185912, 473888, 0]], ![![6170123348, 795930019, 89438528918, 1923343568, -350784], ![-16652811204, 627070791, -241394292248, 698784, 0]], ![![1347498084, 173823733, 19532552927, 420040563, -76608], ![-3636820518, 136946683, -52718295424, 152608, 0]], ![![4312898532, 556352774, 62517275674, 1344411648, -245197], ![-11640267292, 438320770, -168733919232, 488448, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-93, 251, 0, 0, 0], ![-136, 0, 251, 0, 0], ![-30, 0, 0, 251, 0], ![-96, 0, 0, 0, 251]], ![![0, 1, 0, 0, 0], ![-35, 93, 1, 0, 0], ![-51, 1, 93, 2, 0], ![-5, -70, -41, 42, 126], ![-34, -27, -16, -20, 144]]]
  hle1 := by decide
  hle2 := by decide

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI251N2: IdealEqSpanCertificate O ℤ timesTableO I251N2
 ![![251, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![243, 1, 0, 0, 0], ![187, 0, 1, 0, 0], ![250, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 1, -8, 2, 0], ![15, -70, -41, -59, 126], ![3, -27, -16, -20, 43]]]
  hmulB := by decide
  f := ![![![179863991, -1236677167, 9739507964, -2434210550, -1354500], ![5648291905, 78308486, 305573022400, 2698250, 0]], ![![174827786, -1202050187, 9466801638, -2366052629, -1316574], ![5490139316, 76116001, 297016974560, 2622699, 0]], ![![134538250, -925034496, 7285151803, -1820789453, -1013166], ![4224921866, 58574867, 228568615936, 2018291, 0]], ![![179144537, -1231730451, 9700549932, -2424473708, -1349082], ![5625698799, 77995493, 304350730336, 2687457, 0]], ![![50161278, -344890046, 2716197440, -678863500, -377749], ![1575221026, 21839060, 85219568000, 752500, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-243, 251, 0, 0, 0], ![-187, 0, 251, 0, 0], ![-250, 0, 0, 251, 0], ![-70, 0, 0, 0, 251]], ![![-1, 1, 0, 0, 0], ![7, -8, 1, 0, 0], ![3, 1, -8, 2, 0], ![122, -70, -41, -59, 126], ![46, -27, -16, -20, 43]]]
  hle1 := by decide
  hle2 := by decide

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulEqCertificate O ℤ timesTableO (I251N0) I251N1
  ![![251, 0, 0, 0, 0], ![-433, -295, -114, -143, 372]] ![![251, 0, 0, 0, 0], ![93, 1, 0, 0, 0]]
  ![![251, 0, 0, 0, 0], ![-1706, -1078, -599, -786, 2058]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![63001, 0, 0, 0, 0], ![23343, 251, 0, 0, 0]], ![![-108683, -74045, -28614, -35893, 93372], ![-41298, -28016, -10986, -13674, 35550]]]
 hmul := by decide
 f :=  ![![![![522009877413026737522297198, 66390145406368209986893468, 7450916850765858167483894961, 160239207131008969096134310, -107645782729832532852], ![-1408865402658022222953185847, 52204074348241558263902833, -20110024998114543316966454892, 214437034964843287904, 0]], ![![67364563729234, 0, 0, 0, 0], ![29618, 0, 0, 0, 0]]], ![![![-3548004132716335696879493664, -451241481178062196736632789, -50642497245557567180148896892, -1089116113935473823358369739, 731648381612404316526], ![9575796335203571810004411721, -354821392365419123172709299, 136684102906131470716782919824, -1457488678247211727264, 0]], ![![-457864421444357, 0, 0, 0, 0], ![-201308, 0, 0, 0, 0]]]]
 g :=  ![![![![251, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![93, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![1273, 783, 485, 643, -1686], ![251, 0, 0, 0, 0]], ![![1256, 786, 455, 600, -1572], ![209, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI251N1 : IdealMulEqCertificate O ℤ timesTableO (I251N0*I251N1) I251N2
  ![![251, 0, 0, 0, 0], ![-1706, -1078, -599, -786, 2058]] ![![251, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![251, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI251N0
 hI2 := rfl
 M :=  ![![![63001, 0, 0, 0, 0], ![-2008, 251, 0, 0, 0]], ![![-428206, -270578, -150349, -197286, 516558], ![8032, 5773, 3012, 4016, -10542]]]
 hmul := by decide
 f :=  ![![![![6028689937787134957, -854036687684105217, 812515942440689344, -203100153642509914, -113013944539692], ![189150568917011579103, 33413973335667070, 25495710644667234880, 225130846075446, 0]], ![![6547112, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![251, 0, 0, 0, 0]], ![![-8, 1, 0, 0, 0]]], ![![![-1706, -1078, -599, -786, 2058]], ![![32, 23, 12, 16, -42]]]]
 hle1 := by decide
 hle2 := by decide

def PBC251 : PrimesBelowPCertificate 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI251N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

