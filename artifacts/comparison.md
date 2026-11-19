### LOAD

求解栏依次为根区域 unknown／timeout、含嵌套区域 unknown／timeout、原生 Z3 check 超时。

| 分钟 | 本轮正常终态／队列／RSS GiB | 带 SMT 首轮终态／队列／RSS GiB | 无 SMT 第三轮终态／队列／RSS GiB | 本轮／首轮共享 load1 | 本轮求解栏 | 首轮求解栏 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 2／1295／12.19 | 112／49／11.61 | 350／234／7.77 | 167.17／123.00 | 58／0 · 77／0 · 0 | 195／0 · 392／0 · 0 |
| 30 | 21／919／12.33 | 193／23／12.57 | 396／396／8.72 | 146.04／181.20 | 77／3 · 115／3 · 0 | 276／7 · 551／13 · 0 |
| 45 | 25／186／17.70 | 245／22／13.08 | 424／468／9.20 | 115.04／201.16 | 103／3 · 144／3 · 0 | 342／12 · 689／22 · 0 |
| 60 | 28／250／21.20 | 287／50／14.44 | 424／520／9.34 | 108.03／157.26 | 112／3 · 153／3 · 0 | 441／24 · 877／34 · 0 |
| 75 | 28／20／22.08 | 304／30／15.33 | 452／586／9.81 | 110.13／238.77 | 115／4 · 156／4 · 0 | 453／31 · 910／41 · 0 |
| 90 | 29／125／23.34 | 315／17／16.48 | 462／670／10.19 | 107.21／233.20 | 123／5 · 167／5 · 0 | 468／34 · 949／44 · 0 |
| 105 | 51／161／26.42 | 321／16／17.70 | 500／745／10.61 | 111.75／276.19 | 160／6 · 235／6 · 0 | 484／37 · 979／47 · 0 |
| 120 | 88／10／29.17 | 326／15／18.88 | 518／765／10.63 | 91.27／231.10 | 204／7 · 323／7 · 0 | 499／41 · 1015／51 · 0 |

| 区域标签 | 站点 | 本轮根／含嵌套 | SMT 首轮根／含嵌套 |
| --- | --- | ---: | ---: |
| solver_unknown | `phys_access_check@5` | 21／21 | 126／126 |
| solver_unknown | `phys_access_check@9` | 0／27 | 0／169 |
| solver_unknown | `phys_access_check@15` | 0／34 | 0／219 |
| solver_unknown | `pmaCheck@3` | 12／20 | 69／87 |
| solver_unknown | `translationMode@56` | 22／45 | 18／40 |
| solver_unknown | `translationMode@2` | 23／23 | 22／22 |
| solver_unknown | `translateAddrWithPBMT@13` | 21／21 | 15／15 |
| solver_unknown | `translate_TLB_miss@34` | 19／19 | 14／14 |
| solver_unknown | `pt_walk@236` | 8／16 | 9／23 |
| solver_unknown | `pt_walk@386` | 5／12 | 5／10 |
| solver_unknown | `phys_access_check@10` | 7／7 | 50／50 |
| solver_unknown | `phys_access_check@6` | 6／6 | 43／43 |
| solver_unknown | `set_X@16` | 4／4 | 29／29 |
| solver_unknown | `translationMode@10` | 0／0 | 0／22 |
| timeout | `phys_access_check@5` | 2／2 | 11／11 |
| timeout | `matching_pma_bits_range@22` | 1／1 | 2／2 |
| timeout | `phys_access_check@6` | 1／1 | 9／9 |
| timeout | `pmaCheck@19` | 1／1 | 0／0 |
| timeout | `pmaCheck@3` | 1／1 | 0／0 |
| timeout | `pmpCheck@80` | 1／1 | 2／4 |
| timeout | `checked_mem_read@13` | 0／0 | 3／3 |
| timeout | `clint_load@38` | 0／0 | 1／1 |
| timeout | `clint_load@56` | 0／0 | 1／1 |
| timeout | `phys_access_check@10` | 0／0 | 1／1 |
| timeout | `within_mmio_readable@6` | 0／0 | 7／7 |
| timeout | `pt_walk@236` | 0／0 | 3／3 |
| timeout | `pmpMatchAddr@15` | 0／0 | 0／2 |
| timeout | `pmpMatchAddr@18` | 0／0 | 0／2 |

### STORE

求解栏依次为根区域 unknown／timeout、含嵌套区域 unknown／timeout、原生 Z3 check 超时。

| 分钟 | 本轮正常终态／队列／RSS GiB | 带 SMT 首轮终态／队列／RSS GiB | 无 SMT 第三轮终态／队列／RSS GiB | 本轮／首轮共享 load1 | 本轮求解栏 | 首轮求解栏 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 1／1288／10.63 | 134／36／10.02 | — | 167.17／123.00 | 65／0 · 89／0 · 0 | 200／0 · 432／0 · 0 |
| 30 | 1／1649／11.03 | 225／26／11.31 | — | 146.04／181.20 | 65／0 · 89／0 · 0 | 307／4 · 644／4 · 0 |
| 45 | 5／59／15.95 | 262／19／11.96 | — | 115.04／201.16 | 94／0 · 120／0 · 0 | 370／13 · 755／13 · 0 |
| 60 | 7／59／20.39 | 319／30／13.76 | — | 108.67／157.26 | 104／0 · 130／0 · 0 | 446／17 · 927／17 · 0 |
| 75 | 10／173／24.05 | 348／16／15.38 | — | 110.13／238.77 | 124／2 · 154／2 · 0 | 490／24 · 1000／25 · 0 |
| 90 | 12／172／25.59 | 376／42／16.11 | — | 107.21／233.20 | 132／2 · 162／2 · 0 | 549／28 · 1128／30 · 0 |
| 105 | 14／0／27.81 | 386／20／17.05 | — | 111.75／276.19 | 152／2 · 182／2 · 0 | 560／35 · 1156／37 · 0 |
| 120 | 15／0／27.77 | 394／13／17.86 | — | 91.27／231.10 | 155／5 · 187／5 · 0 | 573／42 · 1187／47 · 0 |

| 区域标签 | 站点 | 本轮根／含嵌套 | SMT 首轮根／含嵌套 |
| --- | --- | ---: | ---: |
| solver_unknown | `phys_access_check@5` | 2／2 | 150／150 |
| solver_unknown | `phys_access_check@9` | 0／2 | 0／198 |
| solver_unknown | `phys_access_check@15` | 0／2 | 0／253 |
| solver_unknown | `pmaCheck@3` | 3／3 | 82／96 |
| solver_unknown | `translationMode@56` | 28／56 | 21／47 |
| solver_unknown | `translateAddrWithPBMT@13` | 28／28 | 20／20 |
| solver_unknown | `translate_TLB_miss@34` | 28／28 | 16／16 |
| solver_unknown | `translationMode@2` | 28／28 | 26／26 |
| solver_unknown | `translateAddrWithPBMT@104` | 14／14 | 9／9 |
| solver_unknown | `get_X@16` | 12／12 | 12／12 |
| solver_unknown | `split_misaligned@11` | 12／12 | 12／12 |
| solver_unknown | `phys_access_check@10` | 0／0 | 55／55 |
| solver_unknown | `phys_access_check@6` | 0／0 | 48／48 |
| solver_unknown | `MemoryOpResult_add_meta<b>@1` | 0／0 | 16／35 |
| solver_unknown | `pt_walk@236` | 0／0 | 10／29 |
| solver_unknown | `translationMode@10` | 0／0 | 0／26 |
| timeout | `phys_access_check@5` | 4／4 | 13／13 |
| timeout | `matching_pma_bits_range@22` | 1／1 | 3／3 |
| timeout | `checked_mem_read@13` | 0／0 | 1／1 |
| timeout | `clint_store@56` | 0／0 | 1／1 |
| timeout | `clint_store@74` | 0／0 | 1／1 |
| timeout | `misaligned_pma_check@50` | 0／0 | 1／1 |
| timeout | `phys_access_check@10` | 0／0 | 2／2 |
| timeout | `phys_access_check@6` | 0／0 | 11／11 |
| timeout | `pmpCheck@80` | 0／0 | 1／3 |
| timeout | `pmpMatchAddr@15` | 0／0 | 0／1 |
| timeout | `pmpReadAddrReg@42` | 0／0 | 2／3 |
| timeout | `pt_walk@236` | 0／0 | 2／3 |
| timeout | `pt_walk@220` | 0／0 | 2／2 |
| timeout | `within_mmio_readable@6` | 0／0 | 2／2 |
