import proofs.baseline_program.BaselinePrefix
import proofs.baseline_program.BaselineStructure
import proofs.global_lower_bound.LowerBound

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

/-! Auto-generated symbolic prefix scratch evaluation. -/
def prefixScratch (mem : Memory) : Nat → Nat := by
  let s0 := (initCore baselineProgram).scratch
  let s1 := write s0 0 0
  let s2 := write s1 3 (memAt mem (s1 0))
  let s3 := write s2 0 1
  let s4 := write s3 4 (memAt mem (s3 0))
  let s5 := write s4 0 2
  let s6 := write s5 5 (memAt mem (s5 0))
  let s7 := write s6 0 3
  let s8 := write s7 6 (memAt mem (s7 0))
  let s9 := write s8 0 4
  let s10 := write s9 7 (memAt mem (s9 0))
  let s11 := write s10 0 5
  let s12 := write s11 8 (memAt mem (s11 0))
  let s13 := write s12 0 6
  let s14 := write s13 9 (memAt mem (s13 0))
  let s15 := write s14 10 0
  let s16 := write s15 11 1
  let s17 := write s16 12 2
  let s18 := write s17 17 2127912214
  let s19 := write s18 18 12
  let s20 := write s19 19 3345072700
  let s21 := write s20 20 19
  let s22 := write s21 21 374761393
  let s23 := write s22 22 5
  let s24 := write s23 23 3550635116
  let s25 := write s24 24 9
  let s26 := write s25 25 4251993797
  let s27 := write s26 26 3
  let s28 := write s27 27 3042594569
  let s29 := write s28 28 16
  let s30 := write s29 29 4
  let s31 := write s30 30 6
  let s32 := write s31 31 7
  let s33 := write s32 32 8
  let s34 := write s33 33 10
  let s35 := write s34 34 11
  let s36 := write s35 35 13
  let s37 := write s36 36 14
  let s38 := write s37 37 15
  let s39 := write s38 38 17
  let s40 := write s39 39 18
  let s41 := write s40 40 20
  let s42 := write s41 41 21
  let s43 := write s42 42 22
  let s44 := write s43 43 23
  let s45 := write s44 44 24
  let s46 := write s45 45 25
  let s47 := write s46 46 26
  let s48 := write s47 47 27
  let s49 := write s48 48 28
  let s50 := write s49 49 29
  let s51 := write s50 50 30
  let s52 := write s51 51 31
  let s53 := write s52 52 32
  let s54 := write s53 53 33
  let s55 := write s54 54 34
  let s56 := write s55 55 35
  let s57 := write s56 56 36
  let s58 := write s57 57 37
  let s59 := write s58 58 38
  let s60 := write s59 59 39
  let s61 := write s60 60 40
  let s62 := write s61 61 41
  let s63 := write s62 62 42
  let s64 := write s63 63 43
  let s65 := write s64 64 44
  let s66 := write s65 65 45
  let s67 := write s66 66 46
  let s68 := write s67 67 47
  let s69 := write s68 68 48
  let s70 := write s69 69 49
  let s71 := write s70 70 50
  let s72 := write s71 71 51
  let s73 := write s72 72 52
  let s74 := write s73 73 53
  let s75 := write s74 74 54
  let s76 := write s75 75 55
  let s77 := write s76 76 56
  let s78 := write s77 77 57
  let s79 := write s78 78 58
  let s80 := write s79 79 59
  let s81 := write s80 80 60
  let s82 := write s81 81 61
  let s83 := write s82 82 62
  let s84 := write s83 83 63
  let s85 := write s84 84 64
  let s86 := write s85 85 65
  let s87 := write s86 86 66
  let s88 := write s87 87 67
  let s89 := write s88 88 68
  let s90 := write s89 89 69
  let s91 := write s90 90 70
  let s92 := write s91 91 71
  let s93 := write s92 92 72
  let s94 := write s93 93 73
  let s95 := write s94 94 74
  let s96 := write s95 95 75
  let s97 := write s96 96 76
  let s98 := write s97 97 77
  let s99 := write s98 98 78
  let s100 := write s99 99 79
  let s101 := write s100 100 80
  let s102 := write s101 101 81
  let s103 := write s102 102 82
  let s104 := write s103 103 83
  let s105 := write s104 104 84
  let s106 := write s105 105 85
  let s107 := write s106 106 86
  let s108 := write s107 107 87
  let s109 := write s108 108 88
  let s110 := write s109 109 89
  let s111 := write s110 110 90
  let s112 := write s111 111 91
  let s113 := write s112 112 92
  let s114 := write s113 113 93
  let s115 := write s114 114 94
  let s116 := write s115 115 95
  let s117 := write s116 116 96
  let s118 := write s117 117 97
  let s119 := write s118 118 98
  let s120 := write s119 119 99
  let s121 := write s120 120 100
  let s122 := write s121 121 101
  let s123 := write s122 122 102
  let s124 := write s123 123 103
  let s125 := write s124 124 104
  let s126 := write s125 125 105
  let s127 := write s126 126 106
  let s128 := write s127 127 107
  let s129 := write s128 128 108
  let s130 := write s129 129 109
  let s131 := write s130 130 110
  let s132 := write s131 131 111
  let s133 := write s132 132 112
  let s134 := write s133 133 113
  let s135 := write s134 134 114
  let s136 := write s135 135 115
  let s137 := write s136 136 116
  let s138 := write s137 137 117
  let s139 := write s138 138 118
  let s140 := write s139 139 119
  let s141 := write s140 140 120
  let s142 := write s141 141 121
  let s143 := write s142 142 122
  let s144 := write s143 143 123
  let s145 := write s144 144 124
  let s146 := write s145 145 125
  let s147 := write s146 146 126
  let s148 := write s147 147 127
  let s149 := write s148 148 128
  let s150 := write s149 149 129
  let s151 := write s150 150 130
  let s152 := write s151 151 131
  let s153 := write s152 152 132
  let s154 := write s153 153 133
  let s155 := write s154 154 134
  let s156 := write s155 155 135
  let s157 := write s156 156 136
  let s158 := write s157 157 137
  let s159 := write s158 158 138
  let s160 := write s159 159 139
  let s161 := write s160 160 140
  let s162 := write s161 161 141
  let s163 := write s162 162 142
  let s164 := write s163 163 143
  let s165 := write s164 164 144
  let s166 := write s165 165 145
  let s167 := write s166 166 146
  let s168 := write s167 167 147
  let s169 := write s168 168 148
  let s170 := write s169 169 149
  let s171 := write s170 170 150
  let s172 := write s171 171 151
  let s173 := write s172 172 152
  let s174 := write s173 173 153
  let s175 := write s174 174 154
  let s176 := write s175 175 155
  let s177 := write s176 176 156
  let s178 := write s177 177 157
  let s179 := write s178 178 158
  let s180 := write s179 179 159
  let s181 := write s180 180 160
  let s182 := write s181 181 161
  let s183 := write s182 182 162
  let s184 := write s183 183 163
  let s185 := write s184 184 164
  let s186 := write s185 185 165
  let s187 := write s186 186 166
  let s188 := write s187 187 167
  let s189 := write s188 188 168
  let s190 := write s189 189 169
  let s191 := write s190 190 170
  let s192 := write s191 191 171
  let s193 := write s192 192 172
  let s194 := write s193 193 173
  let s195 := write s194 194 174
  let s196 := write s195 195 175
  let s197 := write s196 196 176
  let s198 := write s197 197 177
  let s199 := write s198 198 178
  let s200 := write s199 199 179
  let s201 := write s200 200 180
  let s202 := write s201 201 181
  let s203 := write s202 202 182
  let s204 := write s203 203 183
  let s205 := write s204 204 184
  let s206 := write s205 205 185
  let s207 := write s206 206 186
  let s208 := write s207 207 187
  let s209 := write s208 208 188
  let s210 := write s209 209 189
  let s211 := write s210 210 190
  let s212 := write s211 211 191
  let s213 := write s212 212 192
  let s214 := write s213 213 193
  let s215 := write s214 214 194
  let s216 := write s215 215 195
  let s217 := write s216 216 196
  let s218 := write s217 217 197
  let s219 := write s218 218 198
  let s220 := write s219 219 199
  let s221 := write s220 220 200
  let s222 := write s221 221 201
  let s223 := write s222 222 202
  let s224 := write s223 223 203
  let s225 := write s224 224 204
  let s226 := write s225 225 205
  let s227 := write s226 226 206
  let s228 := write s227 227 207
  let s229 := write s228 228 208
  let s230 := write s229 229 209
  let s231 := write s230 230 210
  let s232 := write s231 231 211
  let s233 := write s232 232 212
  let s234 := write s233 233 213
  let s235 := write s234 234 214
  let s236 := write s235 235 215
  let s237 := write s236 236 216
  let s238 := write s237 237 217
  let s239 := write s238 238 218
  let s240 := write s239 239 219
  let s241 := write s240 240 220
  let s242 := write s241 241 221
  let s243 := write s242 242 222
  let s244 := write s243 243 223
  let s245 := write s244 244 224
  let s246 := write s245 245 225
  let s247 := write s246 246 226
  let s248 := write s247 247 227
  let s249 := write s248 248 228
  let s250 := write s249 249 229
  let s251 := write s250 250 230
  let s252 := write s251 251 231
  let s253 := write s252 252 232
  let s254 := write s253 253 233
  let s255 := write s254 254 234
  let s256 := write s255 255 235
  let s257 := write s256 256 236
  let s258 := write s257 257 237
  let s259 := write s258 258 238
  let s260 := write s259 259 239
  let s261 := write s260 260 240
  let s262 := write s261 261 241
  let s263 := write s262 262 242
  let s264 := write s263 263 243
  let s265 := write s264 264 244
  let s266 := write s265 265 245
  let s267 := write s266 266 246
  let s268 := write s267 267 247
  let s269 := write s268 268 248
  let s270 := write s269 269 249
  let s271 := write s270 270 250
  let s272 := write s271 271 251
  let s273 := write s272 272 252
  let s274 := write s273 273 253
  let s275 := write s274 274 254
  let s276 := write s275 275 255
  exact s276

section
  variable (mem : Memory)
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 1 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 2 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 3 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 4 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 5 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_0 : prefixScratch mem 0 = 6 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_10 : prefixScratch mem 10 = 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_11 : prefixScratch mem 11 = 1 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_12 : prefixScratch mem 12 = 2 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_17 : prefixScratch mem 17 = 2127912214 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_18 : prefixScratch mem 18 = 12 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_19 : prefixScratch mem 19 = 3345072700 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_20 : prefixScratch mem 20 = 19 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_21 : prefixScratch mem 21 = 374761393 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_22 : prefixScratch mem 22 = 5 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_23 : prefixScratch mem 23 = 3550635116 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_24 : prefixScratch mem 24 = 9 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_25 : prefixScratch mem 25 = 4251993797 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_26 : prefixScratch mem 26 = 3 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_27 : prefixScratch mem 27 = 3042594569 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_28 : prefixScratch mem 28 = 16 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_29 : prefixScratch mem 29 = 4 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_30 : prefixScratch mem 30 = 6 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_31 : prefixScratch mem 31 = 7 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_32 : prefixScratch mem 32 = 8 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_33 : prefixScratch mem 33 = 10 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_34 : prefixScratch mem 34 = 11 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_35 : prefixScratch mem 35 = 13 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_36 : prefixScratch mem 36 = 14 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_37 : prefixScratch mem 37 = 15 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_38 : prefixScratch mem 38 = 17 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_39 : prefixScratch mem 39 = 18 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_40 : prefixScratch mem 40 = 20 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_41 : prefixScratch mem 41 = 21 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_42 : prefixScratch mem 42 = 22 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_43 : prefixScratch mem 43 = 23 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_44 : prefixScratch mem 44 = 24 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_45 : prefixScratch mem 45 = 25 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_46 : prefixScratch mem 46 = 26 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_47 : prefixScratch mem 47 = 27 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_48 : prefixScratch mem 48 = 28 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_49 : prefixScratch mem 49 = 29 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_50 : prefixScratch mem 50 = 30 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_51 : prefixScratch mem 51 = 31 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_52 : prefixScratch mem 52 = 32 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_53 : prefixScratch mem 53 = 33 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_54 : prefixScratch mem 54 = 34 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_55 : prefixScratch mem 55 = 35 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_56 : prefixScratch mem 56 = 36 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_57 : prefixScratch mem 57 = 37 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_58 : prefixScratch mem 58 = 38 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_59 : prefixScratch mem 59 = 39 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_60 : prefixScratch mem 60 = 40 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_61 : prefixScratch mem 61 = 41 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_62 : prefixScratch mem 62 = 42 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_63 : prefixScratch mem 63 = 43 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_64 : prefixScratch mem 64 = 44 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_65 : prefixScratch mem 65 = 45 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_66 : prefixScratch mem 66 = 46 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_67 : prefixScratch mem 67 = 47 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_68 : prefixScratch mem 68 = 48 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_69 : prefixScratch mem 69 = 49 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_70 : prefixScratch mem 70 = 50 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_71 : prefixScratch mem 71 = 51 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_72 : prefixScratch mem 72 = 52 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_73 : prefixScratch mem 73 = 53 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_74 : prefixScratch mem 74 = 54 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_75 : prefixScratch mem 75 = 55 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_76 : prefixScratch mem 76 = 56 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_77 : prefixScratch mem 77 = 57 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_78 : prefixScratch mem 78 = 58 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_79 : prefixScratch mem 79 = 59 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_80 : prefixScratch mem 80 = 60 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_81 : prefixScratch mem 81 = 61 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_82 : prefixScratch mem 82 = 62 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_83 : prefixScratch mem 83 = 63 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_84 : prefixScratch mem 84 = 64 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_85 : prefixScratch mem 85 = 65 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_86 : prefixScratch mem 86 = 66 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_87 : prefixScratch mem 87 = 67 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_88 : prefixScratch mem 88 = 68 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_89 : prefixScratch mem 89 = 69 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_90 : prefixScratch mem 90 = 70 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_91 : prefixScratch mem 91 = 71 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_92 : prefixScratch mem 92 = 72 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_93 : prefixScratch mem 93 = 73 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_94 : prefixScratch mem 94 = 74 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_95 : prefixScratch mem 95 = 75 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_96 : prefixScratch mem 96 = 76 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_97 : prefixScratch mem 97 = 77 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_98 : prefixScratch mem 98 = 78 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_99 : prefixScratch mem 99 = 79 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_100 : prefixScratch mem 100 = 80 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_101 : prefixScratch mem 101 = 81 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_102 : prefixScratch mem 102 = 82 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_103 : prefixScratch mem 103 = 83 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_104 : prefixScratch mem 104 = 84 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_105 : prefixScratch mem 105 = 85 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_106 : prefixScratch mem 106 = 86 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_107 : prefixScratch mem 107 = 87 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_108 : prefixScratch mem 108 = 88 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_109 : prefixScratch mem 109 = 89 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_110 : prefixScratch mem 110 = 90 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_111 : prefixScratch mem 111 = 91 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_112 : prefixScratch mem 112 = 92 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_113 : prefixScratch mem 113 = 93 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_114 : prefixScratch mem 114 = 94 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_115 : prefixScratch mem 115 = 95 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_116 : prefixScratch mem 116 = 96 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_117 : prefixScratch mem 117 = 97 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_118 : prefixScratch mem 118 = 98 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_119 : prefixScratch mem 119 = 99 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_120 : prefixScratch mem 120 = 100 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_121 : prefixScratch mem 121 = 101 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_122 : prefixScratch mem 122 = 102 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_123 : prefixScratch mem 123 = 103 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_124 : prefixScratch mem 124 = 104 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_125 : prefixScratch mem 125 = 105 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_126 : prefixScratch mem 126 = 106 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_127 : prefixScratch mem 127 = 107 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_128 : prefixScratch mem 128 = 108 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_129 : prefixScratch mem 129 = 109 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_130 : prefixScratch mem 130 = 110 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_131 : prefixScratch mem 131 = 111 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_132 : prefixScratch mem 132 = 112 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_133 : prefixScratch mem 133 = 113 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_134 : prefixScratch mem 134 = 114 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_135 : prefixScratch mem 135 = 115 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_136 : prefixScratch mem 136 = 116 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_137 : prefixScratch mem 137 = 117 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_138 : prefixScratch mem 138 = 118 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_139 : prefixScratch mem 139 = 119 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_140 : prefixScratch mem 140 = 120 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_141 : prefixScratch mem 141 = 121 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_142 : prefixScratch mem 142 = 122 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_143 : prefixScratch mem 143 = 123 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_144 : prefixScratch mem 144 = 124 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_145 : prefixScratch mem 145 = 125 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_146 : prefixScratch mem 146 = 126 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_147 : prefixScratch mem 147 = 127 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_148 : prefixScratch mem 148 = 128 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_149 : prefixScratch mem 149 = 129 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_150 : prefixScratch mem 150 = 130 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_151 : prefixScratch mem 151 = 131 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_152 : prefixScratch mem 152 = 132 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_153 : prefixScratch mem 153 = 133 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_154 : prefixScratch mem 154 = 134 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_155 : prefixScratch mem 155 = 135 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_156 : prefixScratch mem 156 = 136 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_157 : prefixScratch mem 157 = 137 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_158 : prefixScratch mem 158 = 138 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_159 : prefixScratch mem 159 = 139 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_160 : prefixScratch mem 160 = 140 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_161 : prefixScratch mem 161 = 141 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_162 : prefixScratch mem 162 = 142 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_163 : prefixScratch mem 163 = 143 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_164 : prefixScratch mem 164 = 144 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_165 : prefixScratch mem 165 = 145 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_166 : prefixScratch mem 166 = 146 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_167 : prefixScratch mem 167 = 147 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_168 : prefixScratch mem 168 = 148 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_169 : prefixScratch mem 169 = 149 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_170 : prefixScratch mem 170 = 150 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_171 : prefixScratch mem 171 = 151 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_172 : prefixScratch mem 172 = 152 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_173 : prefixScratch mem 173 = 153 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_174 : prefixScratch mem 174 = 154 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_175 : prefixScratch mem 175 = 155 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_176 : prefixScratch mem 176 = 156 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_177 : prefixScratch mem 177 = 157 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_178 : prefixScratch mem 178 = 158 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_179 : prefixScratch mem 179 = 159 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_180 : prefixScratch mem 180 = 160 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_181 : prefixScratch mem 181 = 161 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_182 : prefixScratch mem 182 = 162 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_183 : prefixScratch mem 183 = 163 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_184 : prefixScratch mem 184 = 164 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_185 : prefixScratch mem 185 = 165 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_186 : prefixScratch mem 186 = 166 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_187 : prefixScratch mem 187 = 167 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_188 : prefixScratch mem 188 = 168 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_189 : prefixScratch mem 189 = 169 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_190 : prefixScratch mem 190 = 170 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_191 : prefixScratch mem 191 = 171 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_192 : prefixScratch mem 192 = 172 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_193 : prefixScratch mem 193 = 173 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_194 : prefixScratch mem 194 = 174 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_195 : prefixScratch mem 195 = 175 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_196 : prefixScratch mem 196 = 176 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_197 : prefixScratch mem 197 = 177 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_198 : prefixScratch mem 198 = 178 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_199 : prefixScratch mem 199 = 179 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_200 : prefixScratch mem 200 = 180 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_201 : prefixScratch mem 201 = 181 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_202 : prefixScratch mem 202 = 182 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_203 : prefixScratch mem 203 = 183 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_204 : prefixScratch mem 204 = 184 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_205 : prefixScratch mem 205 = 185 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_206 : prefixScratch mem 206 = 186 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_207 : prefixScratch mem 207 = 187 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_208 : prefixScratch mem 208 = 188 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_209 : prefixScratch mem 209 = 189 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_210 : prefixScratch mem 210 = 190 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_211 : prefixScratch mem 211 = 191 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_212 : prefixScratch mem 212 = 192 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_213 : prefixScratch mem 213 = 193 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_214 : prefixScratch mem 214 = 194 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_215 : prefixScratch mem 215 = 195 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_216 : prefixScratch mem 216 = 196 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_217 : prefixScratch mem 217 = 197 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_218 : prefixScratch mem 218 = 198 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_219 : prefixScratch mem 219 = 199 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_220 : prefixScratch mem 220 = 200 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_221 : prefixScratch mem 221 = 201 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_222 : prefixScratch mem 222 = 202 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_223 : prefixScratch mem 223 = 203 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_224 : prefixScratch mem 224 = 204 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_225 : prefixScratch mem 225 = 205 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_226 : prefixScratch mem 226 = 206 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_227 : prefixScratch mem 227 = 207 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_228 : prefixScratch mem 228 = 208 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_229 : prefixScratch mem 229 = 209 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_230 : prefixScratch mem 230 = 210 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_231 : prefixScratch mem 231 = 211 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_232 : prefixScratch mem 232 = 212 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_233 : prefixScratch mem 233 = 213 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_234 : prefixScratch mem 234 = 214 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_235 : prefixScratch mem 235 = 215 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_236 : prefixScratch mem 236 = 216 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_237 : prefixScratch mem 237 = 217 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_238 : prefixScratch mem 238 = 218 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_239 : prefixScratch mem 239 = 219 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_240 : prefixScratch mem 240 = 220 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_241 : prefixScratch mem 241 = 221 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_242 : prefixScratch mem 242 = 222 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_243 : prefixScratch mem 243 = 223 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_244 : prefixScratch mem 244 = 224 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_245 : prefixScratch mem 245 = 225 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_246 : prefixScratch mem 246 = 226 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_247 : prefixScratch mem 247 = 227 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_248 : prefixScratch mem 248 = 228 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_249 : prefixScratch mem 249 = 229 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_250 : prefixScratch mem 250 = 230 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_251 : prefixScratch mem 251 = 231 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_252 : prefixScratch mem 252 = 232 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_253 : prefixScratch mem 253 = 233 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_254 : prefixScratch mem 254 = 234 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_255 : prefixScratch mem 255 = 235 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_256 : prefixScratch mem 256 = 236 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_257 : prefixScratch mem 257 = 237 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_258 : prefixScratch mem 258 = 238 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_259 : prefixScratch mem 259 = 239 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_260 : prefixScratch mem 260 = 240 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_261 : prefixScratch mem 261 = 241 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_262 : prefixScratch mem 262 = 242 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_263 : prefixScratch mem 263 = 243 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_264 : prefixScratch mem 264 = 244 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_265 : prefixScratch mem 265 = 245 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_266 : prefixScratch mem 266 = 246 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_267 : prefixScratch mem 267 = 247 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_268 : prefixScratch mem 268 = 248 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_269 : prefixScratch mem 269 = 249 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_270 : prefixScratch mem 270 = 250 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_271 : prefixScratch mem 271 = 251 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_272 : prefixScratch mem 272 = 252 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_273 : prefixScratch mem 273 = 253 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_274 : prefixScratch mem 274 = 254 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_const_275 : prefixScratch mem 275 = 255 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_3 : prefixScratch mem 3 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_4 : prefixScratch mem 4 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_5 : prefixScratch mem 5 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_6 : prefixScratch mem 6 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_7 : prefixScratch mem 7 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_8 : prefixScratch mem 8 = memAt mem 0 := by
    simp [prefixScratch, write]
  @[simp] lemma prefixScratch_load_9 : prefixScratch mem 9 = memAt mem 0 := by
    simp [prefixScratch, write]
end
