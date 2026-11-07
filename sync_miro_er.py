#!/usr/bin/env python3
"""
sync_miro_er.py
Mantém um diagrama ER no Miro sincronizado com a estrutura de um banco PostgreSQL.

O que ele lê: só o catálogo do PostgreSQL (nomes de tabelas, colunas, tipos,
chaves primárias e estrangeiras). Nenhuma linha de dados é consultada, e a
conexão é aberta em modo somente leitura.

O que ele faz no Miro:
  - um frame colorido por schema (ccih, ministerio, ...);
  - uma caixa por tabela, com "coluna: tipo" e marcação [PK] / [FK];
  - um conector por relacionamento (pé de galinha: N do lado da FK, 1 do lado
    da tabela referenciada). Relações vindas do arquivo de configuração ficam
    contínuas; relações inferidas pelo nome da coluna ficam tracejadas.

Rodando de novo, ele só mexe no que mudou: tabela nova entra numa linha nova
no fim do frame, coluna nova atualiza o texto da caixa, tabela removida some.
As posições que vocês ajustarem à mão no Miro são preservadas.

Uso:
    export PG_DSN="host=localhost port=5432 dbname=NOME user=USUARIO_LEITURA password=..."
    export MIRO_TOKEN="..."                                  # nunca no código

    python sync_miro_er.py --config config.toml --dry-run    # só mostra o plano
    python sync_miro_er.py --config config.toml              # sincroniza o board
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path

try:
    import tomllib  # Python 3.11+
except ModuleNotFoundError:  # Python 3.8–3.10
    import tomli as tomllib  # type: ignore

CORES_PADRAO = ["#E3F2FD", "#E8F5E9", "#FFF3E0", "#F3E5F5", "#E0F7FA",
                "#FCE4EC", "#F1F8E9", "#FFFDE7", "#EDE7F6", "#ECEFF1"]


# --------------------------------------------------------------------------
# Modelo
# --------------------------------------------------------------------------
@dataclass
class Coluna:
    nome: str
    tipo: str
    pk: bool = False
    fk: bool = False


@dataclass
class Tabela:
    schema: str
    nome: str
    colunas: list
    view: bool = False

    @property
    def chave(self) -> str:
        return f"{self.schema}.{self.nome}"


@dataclass(frozen=True)
class Relacao:
    origem: str              # tabela com a FK ("schema.tabela")
    colunas: tuple
    destino: str             # tabela referenciada
    colunas_destino: tuple
    tipo: str                # "fk" | "manual" | "inferida"

    @property
    def chave(self) -> str:
        return (f"{self.origem}({','.join(self.colunas)})->"
                f"{self.destino}({','.join(self.colunas_destino)})")


# --------------------------------------------------------------------------
# Leitura do catálogo (somente estrutura)
# --------------------------------------------------------------------------
SQL_COLUNAS = """
SELECT n.nspname, c.relname, c.relkind::text, a.attname,
       pg_catalog.format_type(a.atttypid, a.atttypmod)
FROM pg_catalog.pg_class c
JOIN pg_catalog.pg_namespace n ON n.oid = c.relnamespace
JOIN pg_catalog.pg_attribute a ON a.attrelid = c.oid
WHERE n.nspname = ANY(%(schemas)s)
  AND c.relkind::text = ANY(%(tipos)s)
  AND NOT c.relispartition
  AND a.attnum > 0 AND NOT a.attisdropped
ORDER BY n.nspname, c.relname, a.attnum
"""

SQL_CHAVES = """
SELECT con.contype::text, n.nspname, c.relname,
       ARRAY(SELECT a.attname::text
             FROM unnest(con.conkey) WITH ORDINALITY AS k(attnum, ord)
             JOIN pg_catalog.pg_attribute a
               ON a.attrelid = con.conrelid AND a.attnum = k.attnum
             ORDER BY k.ord),
       fn.nspname, fc.relname,
       ARRAY(SELECT a.attname::text
             FROM unnest(con.confkey) WITH ORDINALITY AS k(attnum, ord)
             JOIN pg_catalog.pg_attribute a
               ON a.attrelid = con.confrelid AND a.attnum = k.attnum
             ORDER BY k.ord)
FROM pg_catalog.pg_constraint con
JOIN pg_catalog.pg_class c ON c.oid = con.conrelid
JOIN pg_catalog.pg_namespace n ON n.oid = c.relnamespace
LEFT JOIN pg_catalog.pg_class fc ON fc.oid = con.confrelid
LEFT JOIN pg_catalog.pg_namespace fn ON fn.oid = fc.relnamespace
WHERE con.contype IN ('p', 'f')
  AND n.nspname = ANY(%(schemas)s)
ORDER BY n.nspname, c.relname, con.conname
"""


def abreviar_tipo(tipo: str) -> str:
    t = tipo
    t = re.sub(r"^timestamp(\(\d+\))? without time zone$", r"timestamp\1", t)
    t = re.sub(r"^timestamp(\(\d+\))? with time zone$", r"timestamptz\1", t)
    t = re.sub(r"^time(\(\d+\))? without time zone$", r"time\1", t)
    t = re.sub(r"^time(\(\d+\))? with time zone$", r"timetz\1", t)
    t = t.replace("character varying", "varchar")
    t = re.sub(r"^character(\(\d+\))?$", r"char\1", t)
    t = t.replace("double precision", "float8")
    return t


def filtro_exclusao(cfg: dict):
    """Monta a função que diz se uma tabela fica de fora do diagrama.
    Padrões no estilo do Finder/terminal: * = qualquer coisa, ? = um caractere.
    Valem para o nome da tabela ou para "schema.tabela"."""
    from fnmatch import fnmatchcase
    globais = list(cfg.get("excluir_tabelas", []))
    por_schema = {s["nome"]: list(s.get("excluir", [])) for s in cfg.get("schemas", [])}

    def excluida(schema: str, nome: str) -> bool:
        chave = f"{schema}.{nome}"
        for p in globais + por_schema.get(schema, []):
            if fnmatchcase(nome, p) or fnmatchcase(chave, p):
                return True
        return False
    return excluida


def ler_catalogo(dsn: str, schemas: list, incluir_views: bool, excluida=lambda s, n: False):
    import psycopg2  # importado aqui para o --help funcionar sem o pacote

    tipos = ["r", "p"] + (["v", "m"] if incluir_views else [])
    conn = psycopg2.connect(dsn)
    try:
        conn.set_session(readonly=True, autocommit=True)
        with conn.cursor() as cur:
            cur.execute(SQL_COLUNAS, {"schemas": schemas, "tipos": tipos})
            linhas_col = cur.fetchall()
            cur.execute(SQL_CHAVES, {"schemas": schemas})
            linhas_con = cur.fetchall()
    finally:
        conn.close()

    tabelas = {}
    for schema, nome, relkind, coluna, tipo in linhas_col:
        if excluida(schema, nome):
            continue
        chave = f"{schema}.{nome}"
        if chave not in tabelas:
            tabelas[chave] = Tabela(schema, nome, [], view=relkind in ("v", "m"))
        tabelas[chave].colunas.append(Coluna(coluna, abreviar_tipo(tipo)))

    relacoes, fora_do_escopo = [], []
    for contype, schema, nome, cols, fschema, fnome, fcols in linhas_con:
        tab = tabelas.get(f"{schema}.{nome}")
        if tab is None:
            continue
        marcar = {c.nome: c for c in tab.colunas}
        for c in cols:
            if c in marcar:
                if contype == "p":
                    marcar[c].pk = True
                else:
                    marcar[c].fk = True
        if contype == "f":
            destino = f"{fschema}.{fnome}"
            if destino not in tabelas:
                fora_do_escopo.append(f"{tab.chave} -> {destino}")
                continue
            relacoes.append(Relacao(tab.chave, tuple(cols), destino, tuple(fcols), "fk"))
    return tabelas, relacoes, fora_do_escopo


def relacoes_manuais(cfg: dict, tabelas: dict, avisos: list):
    rels = []
    for r in cfg.get("relacoes", []):
        origem, destino = r["origem"], r["destino"]
        cols = tuple(r["colunas"])
        dcols = tuple(r.get("colunas_destino", r["colunas"]))
        if origem not in tabelas or destino not in tabelas:
            avisos.append(f"relação manual ignorada (tabela não encontrada): {origem} -> {destino}")
            continue
        nomes_o = {c.nome for c in tabelas[origem].colunas}
        nomes_d = {c.nome for c in tabelas[destino].colunas}
        faltando = [c for c in cols if c not in nomes_o] + [c for c in dcols if c not in nomes_d]
        if faltando:
            avisos.append(f"relação manual ignorada (coluna não encontrada: {', '.join(faltando)}): "
                          f"{origem} -> {destino}")
            continue
        for c in tabelas[origem].colunas:
            if c.nome in cols:
                c.fk = True
        rels.append(Relacao(origem, cols, destino, dcols, "manual"))
    return rels


def relacoes_inferidas(tabelas: dict, ja_existentes: list, avisos: list):
    """Coluna com o mesmo nome da PK simples de outra tabela (ex.: id_hospital).
    PKs chamadas só de "id" não entram, porque não dizem a qual tabela pertencem."""
    donos = {}
    for t in tabelas.values():
        pks = [c.nome for c in t.colunas if c.pk]
        if len(pks) == 1 and pks[0].lower() != "id":
            donos.setdefault(pks[0], []).append(t.chave)
    cobertas = {(r.origem, r.colunas[0]) for r in ja_existentes if len(r.colunas) == 1}
    rels = []
    for nome_pk, lista in donos.items():
        if len(lista) > 1:
            avisos.append(f"inferência ignorada para '{nome_pk}': é PK em várias tabelas ({', '.join(lista)})")
            continue
        destino = lista[0]
        for t in tabelas.values():
            if t.chave == destino or (t.chave, nome_pk) in cobertas:
                continue
            for c in t.colunas:
                if c.nome == nome_pk:
                    c.fk = True
                    rels.append(Relacao(t.chave, (nome_pk,), destino, (nome_pk,), "inferida"))
    return rels


# --------------------------------------------------------------------------
# Aparência das caixas
# --------------------------------------------------------------------------
def linha_coluna_txt(c: Coluna) -> str:
    marca = "  [PK]" if c.pk else ("  [FK]" if c.fk else "")
    if c.pk and c.fk:
        marca = "  [PK, FK]"
    return f"{c.nome}: {c.tipo}{marca}"


def medidas(t: Tabela, lay: dict):
    fonte = lay["fonte"]
    larg_char = fonte * 0.56
    textos = [t.nome + (" (view)" if t.view else "")] + [linha_coluna_txt(c) for c in t.colunas]
    maior = max(len(s) for s in textos)
    w = int(min(max(maior * larg_char + 48, lay["largura_min"]), lay["largura_max"]))
    h = int(lay["respiro"] * 2 + (len(t.colunas) + 2) * lay["altura_linha"])
    return w, h


def conteudo_html(t: Tabela, w: int, lay: dict) -> str:
    e = html.escape
    titulo = f"<strong>{e(t.nome)}</strong>" + (" <em>(view)</em>" if t.view else "")
    traco = "─" * max(8, int((w - 48) / (lay["fonte"] * 0.9)))
    partes = [f"<p>{titulo}</p>", f"<p>{traco}</p>"]
    for c in t.colunas:
        nome = e(c.nome)
        if c.pk:
            nome = f"<u><strong>{nome}</strong></u>"
        elif c.fk:
            nome = f"<em>{nome}</em>"
        marca = ""
        if c.pk and c.fk:
            marca = " [PK, FK]"
        elif c.pk:
            marca = " [PK]"
        elif c.fk:
            marca = " [FK]"
        partes.append(f"<p>{nome}: {e(c.tipo)}{e(marca)}</p>")
    return "".join(partes)


def assinatura(conteudo: str, w: int, h: int) -> str:
    return hashlib.sha1(f"{conteudo}|{w}|{h}".encode()).hexdigest()[:16]


# --------------------------------------------------------------------------
# Cliente da API do Miro
# --------------------------------------------------------------------------
class MiroErro(Exception):
    def __init__(self, status, corpo):
        super().__init__(f"Miro respondeu {status}: {corpo}")
        self.status = status


class MiroCliente:
    BASE = "https://api.miro.com/v2"

    def __init__(self, token: str, board_id: str):
        import requests
        self.s = requests.Session()
        self.s.headers.update({"Authorization": f"Bearer {token}",
                               "Accept": "application/json",
                               "Content-Type": "application/json"})
        self.board = board_id
        self.chamadas_escrita = 0

    def _req(self, metodo, caminho, corpo=None, params=None):
        url = f"{self.BASE}/boards/{self.board}{caminho}"
        espera = 2
        for tentativa in range(6):
            r = self.s.request(metodo, url, json=corpo, params=params, timeout=60)
            if r.status_code == 429 or r.status_code >= 500:
                time.sleep(espera)
                espera = min(espera * 2, 60)
                continue
            if r.status_code >= 400:
                raise MiroErro(r.status_code, r.text[:500])
            return r.json() if r.content else None
        raise MiroErro(r.status_code, "muitas tentativas sem sucesso")

    def _paginar(self, caminho):
        itens, cursor = [], None
        while True:
            params = {"limit": 50}
            if cursor:
                params["cursor"] = cursor
            resp = self._req("GET", caminho, params=params)
            itens.extend(resp.get("data", []))
            cursor = resp.get("cursor")
            if not cursor:
                return itens

    def listar_itens(self):
        return self._paginar("/items")

    def listar_conectores(self):
        return self._paginar("/connectors")

    def criar(self, tipo, corpo):
        self.chamadas_escrita += 1
        return self._req("POST", f"/{tipo}", corpo)

    def atualizar(self, tipo, item_id, corpo):
        self.chamadas_escrita += 1
        return self._req("PATCH", f"/{tipo}/{item_id}", corpo)

    def remover(self, tipo, item_id):
        self.chamadas_escrita += 1
        try:
            self._req("DELETE", f"/{tipo}/{item_id}")
        except MiroErro as e:
            if e.status != 404:
                raise


def normalizar_board_id(valor: str) -> str:
    valor = valor.strip()
    m = re.search(r"/board/([^/?#]+)", valor)
    return m.group(1) if m else valor


# --------------------------------------------------------------------------
# Sincronização
# --------------------------------------------------------------------------
class Sincronizador:
    def __init__(self, cfg, estado, miro, sem_remover=False, log=print):
        self.cfg = cfg
        self.estado = estado
        self.miro = miro
        self.sem_remover = sem_remover
        self.log = log
        lay = {"fonte": 14, "altura_linha": 22, "respiro": 14, "largura_min": 240,
               "largura_max": 520, "colunas_por_frame": 4, "espaco": 60, "margem": 50,
               "distancia_entre_frames": 250}
        lay.update(cfg.get("layout", {}))
        self.lay = lay
        self.estado.setdefault("frames", {})
        self.estado.setdefault("tabelas", {})
        self.estado.setdefault("conectores", {})

    # ---------------- utilidades de geometria ----------------
    @staticmethod
    def _geo(item):
        g = item.get("geometry", {}) or {}
        p = item.get("position", {}) or {}
        return p.get("x", 0.0), p.get("y", 0.0), g.get("width", 0.0), g.get("height", 0.0)

    def _crescer_frame(self, frame_id, larg_min, alt_min):
        """Aumenta o frame mantendo o canto superior esquerdo no lugar."""
        f = self.itens[frame_id]
        x, y, w, h = self._geo(f)
        nw, nh = max(w, larg_min), max(h, alt_min)
        if nw <= w and nh <= h:
            return True
        esq, topo = x - w / 2, y - h / 2
        corpo = {"geometry": {"width": nw, "height": nh},
                 "position": {"x": esq + nw / 2, "y": topo + nh / 2}}
        try:
            novo = self.miro.atualizar("frames", frame_id, corpo)
        except MiroErro as e:
            self.log(f"  ! não consegui aumentar o frame ({e}). Aumente o frame à mão e rode de novo.")
            return False
        self.itens[frame_id] = novo or {**f, **corpo}
        return True

    def _filhos_do_frame(self, frame_id):
        return [i for i in self.itens.values()
                if (i.get("parent") or {}).get("id") == frame_id]

    # ---------------- fluxo principal ----------------
    def executar(self, tabelas: dict, relacoes: list):
        cfg_schemas = self.cfg["schemas"]
        nomes_schemas = [s["nome"] for s in cfg_schemas]

        self.log("Lendo o board...")
        self.itens = {i["id"]: i for i in self.miro.listar_itens()}
        self.conectores_board = {c["id"]: c for c in self.miro.listar_conectores()}

        graus = {}
        for r in relacoes:
            graus[r.origem] = graus.get(r.origem, 0) + 1
            graus[r.destino] = graus.get(r.destino, 0) + 1

        # -------- remoções primeiro (liberam espaço e conectores) --------
        st_tab = self.estado["tabelas"]
        for chave in list(st_tab):
            schema = chave.split(".", 1)[0]
            if schema not in nomes_schemas or chave in tabelas:
                continue
            tem_alguma = any(t.schema == schema for t in tabelas.values())
            if not tem_alguma:
                self.log(f"  ! o schema '{schema}' não retornou nenhuma tabela; "
                         f"por segurança, nada dele foi removido do board.")
                continue
            if self.sem_remover:
                self.log(f"  - (não removida, --sem-remover) {chave}")
                continue
            self.log(f"  - removendo tabela {chave}")
            self.miro.remover("shapes", st_tab[chave]["id"])
            self.itens.pop(st_tab[chave]["id"], None)
            del st_tab[chave]

        # -------- frames e tabelas, schema por schema --------
        for i, sc in enumerate(cfg_schemas):
            schema = sc["nome"]
            cor = sc.get("cor", CORES_PADRAO[i % len(CORES_PADRAO)])
            titulo = sc.get("titulo", schema)
            do_schema = sorted((t for t in tabelas.values() if t.schema == schema),
                               key=lambda t: (-graus.get(t.chave, 0), t.nome))
            if not do_schema:
                self.log(f"  ! schema '{schema}' sem tabelas visíveis para este usuário.")
                continue

            frame_id = (self.estado["frames"].get(schema) or {}).get("id")
            frame_existe = frame_id in self.itens

            novas, alteradas = [], []
            for t in do_schema:
                w, h = medidas(t, self.lay)
                conteudo = conteudo_html(t, w, self.lay)
                sig = assinatura(conteudo, w, h)
                reg = st_tab.get(t.chave)
                if reg and reg["id"] in self.itens and frame_existe:
                    if reg.get("assinatura") != sig:
                        alteradas.append((t, w, h, conteudo, sig))
                else:
                    if reg and reg["id"] in self.itens:  # frame sumiu mas a caixa ficou
                        self.miro.remover("shapes", reg["id"])
                        self.itens.pop(reg["id"], None)
                    novas.append((t, w, h, conteudo, sig))

            if not frame_existe:
                self._criar_frame_com_tabelas(schema, titulo, cor, novas)
            else:
                for item in alteradas:
                    self._atualizar_tabela(frame_id, *item)
                if novas:
                    self._adicionar_no_fim(frame_id, novas)

        # -------- conectores --------
        self._sincronizar_conectores(relacoes)

    def _corpo_tabela(self, conteudo, w, h, x, y, parent_id):
        corpo = {
            "data": {"shape": "rectangle", "content": conteudo},
            "style": {"fillColor": "#ffffff", "borderColor": "#424242", "borderWidth": "2.0",
                      "color": "#1a1a1a", "fontSize": str(self.lay["fonte"]),
                      "textAlign": "left", "textAlignVertical": "top"},
            "position": {"x": x, "y": y},
            "geometry": {"width": w, "height": h},
        }
        if parent_id:
            corpo["parent"] = {"id": parent_id}
        return corpo

    def _criar_frame_com_tabelas(self, schema, titulo, cor, novas):
        lay = self.lay
        m, gap = lay["margem"], lay["espaco"]
        ncols = max(1, min(lay["colunas_por_frame"], len(novas)))
        larg_col = max(w for _, w, _, _, _ in novas)
        alturas = [0] * ncols
        posicoes = []
        for (t, w, h, conteudo, sig) in novas:
            k = alturas.index(min(alturas))
            x = m + k * (larg_col + gap) + w / 2
            y = m + alturas[k] + h / 2
            alturas[k] += h + gap
            posicoes.append((t, w, h, conteudo, sig, x, y))
        fw = 2 * m + ncols * larg_col + (ncols - 1) * gap
        fh = m + max(alturas) - gap + m

        # frame novo entra à direita de todos os frames que o script já criou
        direita = None
        for reg in self.estado["frames"].values():
            f = self.itens.get(reg.get("id"))
            if f:
                x, y, w, h = self._geo(f)
                direita = max(direita if direita is not None else x + w / 2, x + w / 2)
        esq = 0 if direita is None else direita + lay["distancia_entre_frames"]

        self.log(f"  + criando frame '{titulo}' com {len(novas)} tabela(s)")
        frame = self.miro.criar("frames", {
            "data": {"title": titulo, "format": "custom", "type": "freeform"},
            "style": {"fillColor": cor},
            "position": {"x": esq + fw / 2, "y": fh / 2},
            "geometry": {"width": fw, "height": fh},
        })
        self.itens[frame["id"]] = frame
        self.estado["frames"][schema] = {"id": frame["id"]}

        for (t, w, h, conteudo, sig, x, y) in posicoes:
            item = self.miro.criar("shapes", self._corpo_tabela(conteudo, w, h, x, y, frame["id"]))
            self.itens[item["id"]] = item
            self.estado["tabelas"][t.chave] = {"id": item["id"], "assinatura": sig}

    def _adicionar_no_fim(self, frame_id, novas):
        lay = self.lay
        m, gap = lay["margem"], lay["espaco"]
        _, _, fw, _ = self._geo(self.itens[frame_id])
        fundo = m - gap
        for filho in self._filhos_do_frame(frame_id):
            x, y, w, h = self._geo(filho)
            fundo = max(fundo, y + h / 2)
        y0, x0, alt_linha = fundo + gap, m, 0
        posicoes = []
        for (t, w, h, conteudo, sig) in novas:
            if x0 > m and x0 + w > fw - m:
                x0, y0, alt_linha = m, y0 + alt_linha + gap, 0
            posicoes.append((t, w, h, conteudo, sig, x0 + w / 2, y0 + h / 2))
            x0 += w + gap
            alt_linha = max(alt_linha, h)
        larg_nec = max(fw, max(w for _, w, *_ in novas) + 2 * m)
        alt_nec = y0 + alt_linha + m
        dentro = self._crescer_frame(frame_id, larg_nec, alt_nec)
        for (t, w, h, conteudo, sig, x, y) in posicoes:
            self.log(f"  + nova tabela {t.chave}")
            if dentro:
                corpo = self._corpo_tabela(conteudo, w, h, x, y, frame_id)
            else:  # frame não cresceu: coloca a tabela logo abaixo dele, fora do frame
                fx, fy, ffw, ffh = self._geo(self.itens[frame_id])
                corpo = self._corpo_tabela(conteudo, w, h, fx - ffw / 2 + x,
                                           fy + ffh / 2 + y - fundo, None)
            item = self.miro.criar("shapes", corpo)
            self.itens[item["id"]] = item
            self.estado["tabelas"][t.chave] = {"id": item["id"], "assinatura": sig}

    def _atualizar_tabela(self, frame_id, t, w, h, conteudo, sig):
        reg = self.estado["tabelas"][t.chave]
        item = self.itens[reg["id"]]
        x, y, w0, h0 = self._geo(item)
        # mantém o canto superior esquerdo onde vocês deixaram
        nx, ny = x - w0 / 2 + w / 2, y - h0 / 2 + h / 2
        if (item.get("parent") or {}).get("id") == frame_id:
            self._crescer_frame(frame_id, nx + w / 2 + self.lay["margem"],
                                ny + h / 2 + self.lay["margem"])
        self.log(f"  ~ atualizando {t.chave}")
        novo = self.miro.atualizar("shapes", reg["id"], {
            "data": {"content": conteudo},
            "position": {"x": nx, "y": ny},
            "geometry": {"width": w, "height": h},
        })
        self.itens[reg["id"]] = novo or item
        reg["assinatura"] = sig

    def _sincronizar_conectores(self, relacoes):
        st_con = self.estado["conectores"]
        st_tab = self.estado["tabelas"]
        desejadas = {r.chave: r for r in relacoes
                     if r.origem in st_tab and r.destino in st_tab}

        for chave in list(st_con):
            reg = st_con[chave]
            r = desejadas.get(chave)
            ok = (r is not None and reg["id"] in self.conectores_board
                  and reg.get("tipo") == r.tipo
                  and reg.get("de") == st_tab[r.origem]["id"]
                  and reg.get("para") == st_tab[r.destino]["id"])
            if ok:
                continue
            if r is None and self.sem_remover:
                continue
            if reg["id"] in self.conectores_board:
                self.log(f"  - removendo ligação {chave}")
                self.miro.remover("connectors", reg["id"])
            del st_con[chave]

        for chave, r in desejadas.items():
            if chave in st_con:
                continue
            de, para = st_tab[r.origem]["id"], st_tab[r.destino]["id"]
            self.log(f"  + ligação {chave}" + (" (inferida)" if r.tipo == "inferida" else ""))
            con = self.miro.criar("connectors", {
                "startItem": {"id": de},
                "endItem": {"id": para},
                "shape": "elbowed",
                "style": {"startStrokeCap": "erd_many", "endStrokeCap": "erd_only_one",
                          "strokeColor": "#424242", "strokeWidth": "2.0",
                          "strokeStyle": "dashed" if r.tipo == "inferida" else "normal"},
                "captions": [{"content": html.escape(", ".join(r.colunas))}],
            })
            st_con[chave] = {"id": con["id"], "de": de, "para": para, "tipo": r.tipo}


# --------------------------------------------------------------------------
# Plano (dry-run): compara com o arquivo de estado, sem tocar no Miro
# --------------------------------------------------------------------------
def _listar(itens, prefixo, detalhes, limite=15):
    itens = sorted(itens)
    mostrar = itens if detalhes else itens[:limite]
    for k in mostrar:
        print(f"  {prefixo} {k}")
    if len(itens) > len(mostrar):
        print(f"  ... e mais {len(itens) - len(mostrar)} (use --detalhes para ver todas)")


def mostrar_plano(cfg, estado, tabelas, relacoes, lay_cfg, detalhes=False):
    lay = {"fonte": 14, "altura_linha": 22, "respiro": 14, "largura_min": 240, "largura_max": 520}
    lay.update(lay_cfg)
    st_tab = estado.get("tabelas", {})
    print("\nTabelas por schema:")
    for sc in cfg["schemas"]:
        lista = sorted(t.nome for t in tabelas.values() if t.schema == sc["nome"])
        print(f"  {sc['nome']}: {len(lista)}")
        if detalhes:
            for nome in lista:
                print(f"      {nome}")
    novas, alteradas = [], []
    for t in tabelas.values():
        w, h = medidas(t, lay)
        sig = assinatura(conteudo_html(t, w, lay), w, h)
        if t.chave not in st_tab:
            novas.append(t.chave)
        elif st_tab[t.chave].get("assinatura") != sig:
            alteradas.append(t.chave)
    nomes = [s["nome"] for s in cfg["schemas"]]
    removidas = [k for k in st_tab if k.split(".", 1)[0] in nomes and k not in tabelas]
    por_tipo = {}
    for r in relacoes:
        por_tipo[r.tipo] = por_tipo.get(r.tipo, 0) + 1
    print("\nLigações:", ", ".join(f"{v} {k}" for k, v in sorted(por_tipo.items())) or "nenhuma")
    _listar([f"({r.tipo}) {r.chave}" for r in relacoes], "", detalhes, limite=30)
    print(f"\nComparado com o último sync: {len(novas)} nova(s), "
          f"{len(alteradas)} alterada(s), {len(removidas)} removida(s)")
    if st_tab:  # no primeiro sync tudo é novo; não vale a pena listar
        _listar(novas, "+", detalhes)
        _listar(alteradas, "~", detalhes)
        _listar(removidas, "-", detalhes)


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def carregar_estado(caminho: Path, board_id: str):
    if caminho.exists():
        estado = json.loads(caminho.read_text(encoding="utf-8"))
        if estado.get("board_id") and estado["board_id"] != board_id:
            sys.exit(f"O arquivo de estado {caminho} é de outro board ({estado['board_id']}). "
                     f"Use outro arquivo_estado na configuração.")
        return estado
    return {"board_id": board_id}


def salvar_estado(caminho: Path, estado: dict):
    tmp = caminho.with_suffix(caminho.suffix + ".tmp")
    tmp.write_text(json.dumps(estado, indent=2, ensure_ascii=False), encoding="utf-8")
    tmp.replace(caminho)


def montar_modelo(cfg, dsn):
    schemas = [s["nome"] for s in cfg["schemas"]]
    tabelas, relacoes, fora = ler_catalogo(dsn, schemas, cfg.get("incluir_views", False),
                                           filtro_exclusao(cfg))
    avisos = [f"FK para fora dos schemas configurados (não desenhada): {f}" for f in fora]
    for s in schemas:
        if not any(t.schema == s for t in tabelas.values()):
            avisos.append(f"schema '{s}' não retornou tabelas (nome errado ou sem permissão?)")
    relacoes += relacoes_manuais(cfg, tabelas, avisos)
    if cfg.get("inferir_relacoes", False):
        relacoes += relacoes_inferidas(tabelas, relacoes, avisos)
    # remove duplicatas mantendo a primeira (fk > manual > inferida)
    vistas, unicas = set(), []
    for r in relacoes:
        if r.chave not in vistas:
            vistas.add(r.chave)
            unicas.append(r)
    return tabelas, unicas, avisos


def main():
    ap = argparse.ArgumentParser(description="Sincroniza o diagrama ER do PostgreSQL com um board do Miro.")
    ap.add_argument("--config", default="config.toml")
    ap.add_argument("--dry-run", action="store_true",
                    help="lê o banco e mostra o que mudaria, sem acessar o Miro")
    ap.add_argument("--sem-remover", action="store_true",
                    help="nunca remove tabelas/ligações do board")
    ap.add_argument("--detalhes", action="store_true",
                    help="no --dry-run, lista o nome de todas as tabelas e ligações")
    args = ap.parse_args()

    caminho_cfg = Path(args.config)
    cfg = tomllib.loads(caminho_cfg.read_text(encoding="utf-8"))
    board_id = normalizar_board_id(cfg["board_id"])
    caminho_estado = caminho_cfg.parent / cfg.get("arquivo_estado", "estado_miro.json")
    estado = carregar_estado(caminho_estado, board_id)

    dsn = os.environ.get("PG_DSN")
    if not dsn:
        sys.exit("Defina a variável de ambiente PG_DSN com a conexão do banco.")

    tabelas, relacoes, avisos = montar_modelo(cfg, dsn)
    for a in avisos:
        print(f"aviso: {a}")
    print(f"{len(tabelas)} tabela(s), {len(relacoes)} ligação(ões) lidas do banco.")

    if args.dry_run:
        mostrar_plano(cfg, estado, tabelas, relacoes, cfg.get("layout", {}), args.detalhes)
        return

    token = os.environ.get("MIRO_TOKEN")
    if not token:
        sys.exit("Defina a variável de ambiente MIRO_TOKEN com o token do app do Miro.")
    miro = MiroCliente(token, board_id)
    sync = Sincronizador(cfg, estado, miro, sem_remover=args.sem_remover)
    try:
        sync.executar(tabelas, relacoes)
    finally:
        salvar_estado(caminho_estado, estado)  # guarda os IDs mesmo se algo falhar no meio
    print(f"Pronto. {miro.chamadas_escrita} alteração(ões) enviadas ao Miro.")


if __name__ == "__main__":
    main()
