#!/usr/bin/env python3
"""Exact resonance geometry, with common scales across the narrow-band limit."""
from pathlib import Path
import json
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, Normalize
from matplotlib.lines import Line2D

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "numerics"))
from output_paths import figures_dir, checks_dir
FIG = figures_dir()
plt.rcParams.update({"font.size": 9, "pdf.fonttype": 42, "ps.fonttype": 42,
                     "axes.labelsize": 9})
BLUE, ORANGE, GREEN = "#23659e", "#d97732", "#348b70"
CMAP = LinearSegmentedColormap.from_list("resonance", [BLUE, "#f0f4f5", ORANGE])
NORM = Normalize(vmin=.40, vmax=.60)


def branch(d, u, v):
    t, r = np.cos(u), np.cos(v)
    D = np.sqrt(1-4*d*d+d*d*(t-r)**2)
    return np.arccos(d*(t+r)/(1+D))


def omega(d, x):
    return np.sqrt(1-2*d*np.cos(x))


def verify():
    rng = np.random.default_rng(20260929)
    rows = []
    for d in [.25, .025]:
        u, v = rng.uniform(0, np.pi, (2, 10000))
        s = branch(d, u, v)
        residual = omega(d, s+u)+omega(d, s-u)-omega(d, s+v)-omega(d, s-v)
        symmetry = np.max(np.abs(s-branch(d, v, u)))
        reflection = np.max(np.abs(s+branch(d, np.pi-u, np.pi-v)-np.pi))
        q = np.linspace(0, np.pi, 401)
        pairing = np.max(np.abs(branch(d, q, np.pi-q)-np.pi/2))
        rows.append({"d": d, "points": len(u), "max_energy_residual": float(np.max(np.abs(residual))),
                     "max_swap_symmetry_residual": float(symmetry),
                     "max_reflection_residual": float(reflection),
                     "max_pairing_line_residual": float(pairing),
                     "s_over_pi_min": float(branch(d, 0., 0.)/np.pi),
                     "s_over_pi_max": float(branch(d, np.pi, np.pi)/np.pi)})
        assert max(rows[-1][k] for k in ["max_energy_residual", "max_swap_symmetry_residual",
                                       "max_reflection_residual", "max_pairing_line_residual"]) < 2e-14
    return rows


def make_figure():
    fig = plt.figure(figsize=(7.5, 3.65), facecolor="white")
    fig.subplots_adjust(left=.015, right=.97, bottom=.06, top=.91, wspace=.04)
    grid = np.linspace(0, np.pi, 61)
    u, v = np.meshgrid(grid, grid)
    for index, d in enumerate([.25, .025]):
        ax = fig.add_subplot(1, 2, index+1, projection="3d", computed_zorder=False)
        s = branch(d, u, v)/np.pi
        # A sparse reference grid, not a second fitted resonance surface.
        for x in [0., .5, 1.]:
            ax.plot([x,x], [0,1], [.5,.5], color=".65", lw=.65, ls="--", zorder=1)
            ax.plot([0,1], [x,x], [.5,.5], color=".65", lw=.65, ls="--", zorder=1)
        ax.plot_surface(u/np.pi, v/np.pi, s, facecolors=CMAP(NORM(s)),
                        rstride=1, cstride=1, linewidth=0, antialiased=False,
                        shade=False, alpha=.97, zorder=2)
        ax.plot_wireframe(u/np.pi, v/np.pi, s, rstride=6, cstride=6,
                          color="#345565", alpha=.25, linewidth=.45, zorder=3)
        q = np.linspace(0, np.pi, 500)
        ax.plot(q/np.pi, q/np.pi, branch(d,q,q)/np.pi,
                color=".22", lw=1.25, ls="--", zorder=4)
        ax.plot(q/np.pi, 1-q/np.pi, np.full_like(q,.5),
                color=GREEN, lw=2.0, zorder=5)
        ax.set(xlim=(0,1), ylim=(0,1), zlim=(.4,.6))
        ax.set_xticks([0,.5,1], ["0","0.5","1"])
        ax.set_yticks([0,.5,1], ["0","0.5","1"])
        ax.set_zticks([.4,.5,.6], ["0.40","0.50","0.60"])
        ax.set_xlabel(r"Incoming $u/\pi$", labelpad=2)
        ax.set_ylabel(r"Outgoing $v/\pi$", labelpad=2)
        ax.set_zlabel(r"Pair center $s/\pi$", labelpad=3)
        ax.tick_params(axis="both", labelsize=8, pad=0)
        ax.set_box_aspect((1,1,.66))
        ax.set_proj_type("ortho")
        ax.view_init(elev=27, azim=-132)
        ax.grid(False)
        for axis in [ax.xaxis,ax.yaxis,ax.zaxis]:
            axis.pane.fill=False
            axis.pane.set_edgecolor(".88")
            axis.line.set_color(".65")
        title = "Finite bandwidth" if index == 0 else "Narrow bandwidth"
        ax.set_title(fr"({'ab'[index]}) {title}, $d={d}$", fontsize=10, pad=2)
    fig.legend(handles=[Line2D([0],[0],color=".22",ls="--",lw=1.25,
                              label=r"Exchange: $u=v$"),
                        Line2D([0],[0],color=GREEN,lw=2,
                               label=r"Mirror-pair line: $u+v=\pi$")],
               loc="lower center", bbox_to_anchor=(.5,-.015), ncol=2,
               frameon=False, fontsize=8, columnspacing=2.5)
    for suffix in ["pdf","png"]:
        fig.savefig(FIG/f"resonance_geometry_3d.{suffix}", bbox_inches="tight", dpi=220)
    plt.close(fig)


if __name__ == "__main__":
    checks=verify()
    (checks_dir()/"three-d-resonance-check.json").write_text(json.dumps(checks,indent=2)+"\n")
    make_figure()
    print(json.dumps(checks,indent=2))
