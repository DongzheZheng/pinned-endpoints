#!/usr/bin/env python3
"""Physics-facing figures from analytic curves and existing numerical data."""
from pathlib import Path
import csv
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter
from matplotlib.colors import LinearSegmentedColormap, TwoSlopeNorm

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "numerics"))
from output_paths import figures_dir, plot_results_dir
FIG = figures_dir()
DATA = plot_results_dir()
plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                     "axes.spines.right": False, "pdf.fonttype": 42,
                     "ps.fonttype": 42, "axes.labelsize": 10})
BLUE, ORANGE, GREEN = "#23659e", "#d97732", "#348b70"


def save(fig, name):
    fig.savefig(FIG / f"{name}.pdf")
    fig.savefig(FIG / f"{name}.png", dpi=200)
    plt.close(fig)


def collision_picture():
    fig, axs = plt.subplots(1, 2, figsize=(7.2, 3.0), constrained_layout=True)
    x = np.linspace(-np.pi, np.pi, 800)
    for d, color in [(.02, BLUE), (.10, GREEN), (.25, ORANGE)]:
        axs[0].plot(x/np.pi, np.sqrt(1-2*d*np.cos(x)), color=color,
                    lw=1.8, label=fr"$d={d}$")
    axs[0].set(xlabel=r"Wave number $x/\pi$", ylabel=r"Frequency $\omega_d(x)$",
               title="(a) Phonon dispersion", ylim=(.65, 1.3))
    axs[0].set_xticks([-1, -.5, 0, .5, 1])
    axs[0].legend(frameon=False, fontsize=9, loc="lower left")

    ax = axs[1]
    xx = np.linspace(0, np.pi, 500)
    ax.plot(xx/np.pi, np.sin(2*xx), color=BLUE, lw=1.9)
    ax.axhline(0, color="0.65", lw=.7)
    for a, color, marker in [(.18, ORANGE, "o"), (.35, GREEN, "s")]:
        pts = np.array([a, 1-a])
        vals = np.sin(2*np.pi*pts)
        ax.scatter(pts, vals, s=38, color=color, marker=marker, zorder=4)
        ax.plot(pts, vals, color=color, ls=":", lw=1.1)
    ax.text(.5, 1.02, r"$\phi(x)=\sin 2x$", ha="center", fontsize=10)
    ax.text(.5, -.34, r"$\phi(x)+\phi(\pi-x)=0$", ha="center", fontsize=10,
            transform=ax.transAxes)
    ax.set(xlabel=r"Wave number $x/\pi$", ylabel="Mode weight",
           title="(b) Resonant pairs", xlim=(0, 1), ylim=(-1.15, 1.2))
    ax.set_xticks([0, .25, .5, .75, 1])
    save(fig, "collision_memory_picture")


def read(name):
    with (DATA / name).open() as f:
        return list(csv.DictReader(f))


def weak_physical():
    rows = [r for r in read("ritz_spectra.csv")
            if r["convention"] == "ALS_q_entropy" and int(r["M"]) == 14
            and int(r["n"]) == 768 and float(r["d"]) <= .1]
    trials = [r for r in read("trial_quotients.csv")
              if r["convention"] == "ALS_q_entropy" and int(r["M"]) == 14
              and int(r["n"]) == 768 and float(r["d"]) <= .1]
    fig, axs = plt.subplots(1, 2, figsize=(7.2, 3.0), constrained_layout=True)
    for j, color in [(1, BLUE), (2, GREEN), (3, ORANGE)]:
        rr = sorted((r for r in rows if int(r["eigen_index"]) == j),
                    key=lambda r: float(r["d"]))
        axs[0].semilogx([float(r["d"]) for r in rr],
                      [float(r["ritz"])/float(r["d"]) for r in rr],
                      "o-", ms=4, color=color, label=f"Ritz {j}")
    for name, color, label in [("sin2", BLUE, r"$\phi=\sin 2x$"),
                                ("sin1", ORANGE, r"$\phi=\sin x$")]:
        rr = sorted((r for r in trials if r["trial"] == name),
                    key=lambda r: float(r["d"]))
        ds = [float(r["d"]) for r in rr]
        qs = [float(r["quotient"]) for r in rr]
        rescaled = [q/d if name == "sin2" else q*d for q,d in zip(qs,ds)]
        scale_label = r"$\Gamma_2/d$" if name == "sin2" else r"$d\Gamma_1$"
        axs[1].semilogx(ds, rescaled, "o-", ms=4, color=color, label=scale_label)
        constant = 1152/(25*np.pi**2) if name == "sin2" else 18/np.pi**2
        axs[1].axhline(constant, ls="--", lw=1.0, color=color)
        if name == "sin2":
            axs[0].semilogx(ds, rescaled, "--", lw=1.2, color="0.3", label=r"$\sin 2x$ trial")
    axs[0].set(title="(a) Slow rates", xlabel=r"Harmonic coupling $d$",
               ylabel=r"Rate divided by $d$", ylim=(0, 6.5))
    axs[1].set(title="(b) Initial dissipation", xlabel=r"Harmonic coupling $d$",
               ylabel="Rescaled trial rate", ylim=(1.4,5.1))
    for ax in axs:
        ax.set_xticks([.004, .016, .064], ["0.004", "0.016", "0.064"])
        ax.xaxis.set_minor_formatter(NullFormatter())
        ax.legend(frameon=False, fontsize=8)
        ax.grid(axis="y", which="major", color="0.9", lw=.6)
    axs[0].legend(frameon=False,fontsize=8,loc="center",
                  bbox_to_anchor=(.54,.35),ncol=2)
    save(fig, "weak_physical_memory")


def response_rows(grid):
    return [r for r in read("linear_response_times.csv")
            if int(r["M"]) == 14 and int(r["n"]) == 768 and r["time_grid"] == grid]


def weak_response():
    fig, axs = plt.subplots(1, 2, figsize=(7.2, 3.2), sharey=True)
    rows = [r for r in read("linear_response_spectral_weights.csv")
            if int(r["M"]) == 14 and int(r["n"]) == 768]
    colors = [BLUE, GREEN, ORANGE, "#865aa0"]
    styles = ["-", "--", "-.", ":"]
    tau = np.linspace(0, 4, 501)
    for d, color, ls in zip([.004, .008, .016, .032], colors, styles):
        rr = [r for r in rows if float(r["d"]) == d]
        rates = np.array([float(r["rate"]) for r in rr])
        weights = np.array([float(r["C2_normalized_weight"]) for r in rr])
        for ax, multiplier in zip(axs, [1, 2]):
            response = np.exp(-multiplier*tau[:, None]*rates[None, :]/d) @ weights
            ax.plot(tau, response, color=color, ls=ls, lw=1.8, label=fr"$d={d}$")
    for ax, multiplier in zip(axs, [1, 2]):
        ax.plot(tau, np.exp(-multiplier*1152/(25*np.pi**2)*tau),
                color="0.5", ls=":", lw=1.15, label="Original-trial limiting bound")
        ax.plot(tau, np.exp(-multiplier*2048/(185*np.pi**2)*tau),
                color="0.12", ls="--", lw=1.25, label="Adjusted-trial limiting bound")
        ax.set(xlabel=r"Slow time $\tau=dt$", xlim=(0, 4), ylim=(0, 1.02))
        ax.grid(axis="y", color="0.9", lw=.6)
    axs[0].set(title="(a) Spectral moment", ylabel=r"$C_{2,d,G}(t)$")
    axs[1].set(title="(b) Quadratic entropy deficit", ylabel=r"$\|g_{+,G}(t)\|_2^2/\|g_{+,G}(0)\|_2^2$")
    handles, labels = axs[0].get_legend_handles_labels()
    fig.legend(handles[:4], labels[:4], frameon=False, fontsize=8.5, ncol=4,
               loc="lower center", bbox_to_anchor=(.5, .078))
    fig.legend(handles[4:], labels[4:], frameon=False, fontsize=8, ncol=2,
               loc="lower center", bbox_to_anchor=(.5, .002))
    fig.subplots_adjust(left=.075, right=.985, top=.89, bottom=.29, wspace=.30)
    save(fig, "weak_time_response")


def preparation_memory():
    """Analytic initial spectra and a saved, full Galerkin shape reconstruction."""
    with np.load(DATA / "preparation_memory_galerkin.npz") as data:
        x, tau = data["x"], data["tau"]
        equilibrium, plus, minus = data["equilibrium"], data["W_plus"], data["W_minus"]
        distortion = data["relative_distortion"]
        d, eta = float(data["d"]), float(data["eta"])
    fig = plt.figure(figsize=(7.2, 3.55))
    grid = fig.add_gridspec(1, 2, width_ratios=[1, 1.33], wspace=.15,
                          left=.075, right=.965, bottom=.16, top=.86)
    ax = fig.add_subplot(grid[0, 0])
    ax.plot(x/np.pi, plus, color=ORANGE, lw=1.9, label=r"$W_+$")
    ax.plot(x/np.pi, minus, color=BLUE, lw=1.9, label=r"$W_-$")
    ax.plot(x/np.pi, equilibrium, color="0.25", lw=1.1, ls="--", label=r"$N_d$")
    ax.fill_between(x/np.pi, plus, minus, color="0.85", alpha=.2)
    ax.set(xlabel=r"Wave number $x/\pi$", ylabel="Mode occupation",
           title="(a) Equal conserved densities", xlim=(-1, 1), ylim=(.88, 1.21))
    ax.set_xticks([-1, -.5, 0, .5, 1])
    ax.set_yticks([.9, 1, 1.1])
    ax.text(.5, .96, r"$\rho_0[W_+]=\rho_0[W_-]$"+"\n"+r"$\rho_1[W_+]=\rho_1[W_-]$"
            +"\n"+r"$\mathcal{S}[W_+]=\mathcal{S}[W_-]$",
            ha="center", va="top", transform=ax.transAxes, fontsize=9.5)
    ax.legend(frameon=False, fontsize=9, loc="lower center", ncol=3,
              columnspacing=.9, handlelength=1.6)
    ax.grid(axis="y", color="0.92", lw=.6)

    ax3 = fig.add_subplot(grid[0, 1], projection="3d", computed_zorder=False)
    X, T = np.meshgrid(x/np.pi, tau)
    cmap = LinearSegmentedColormap.from_list("memory_balance", ["#23659e", "#f5f3ee", "#d97732"])
    norm = TwoSlopeNorm(vmin=-1.01, vcenter=0, vmax=1.01)
    ax3.plot_surface(X, T, distortion, facecolors=cmap(norm(distortion)),
                     rcount=49, ccount=121, shade=False, antialiased=True,
                     linewidth=0, alpha=.96, zorder=2)
    # Actual time slices make the early and late profiles readable in depth.
    for index, color, width in [(0, "0.18", 1.0), (40, "0.25", .75), (120, GREEN, 1.1)]:
        ax3.plot(x/np.pi, np.full_like(x, tau[index]), distortion[index],
                 color=color, lw=width, zorder=3)
    ax3.plot([-1, 1], [tau[-1], tau[-1]], [0, 0], color="0.4", ls=":", lw=.8, zorder=3)
    ax3.set(xlabel=r"$x/\pi$", ylabel=r"$\tau=dt$", zlabel=r"$g_{+,G}/\eta$",
            title="(b) Relaxing spectrum",
            xlim=(-1, 1), ylim=(0, 3), zlim=(-1.06, 1.06))
    ax3.set_xticks([-1, 0, 1])
    ax3.set_yticks([0, 1, 2, 3])
    ax3.set_zticks([-1, 0, 1])
    ax3.xaxis.labelpad=1
    ax3.yaxis.labelpad=2
    ax3.zaxis.labelpad=0
    ax3.tick_params(pad=0, labelsize=8)
    ax3.view_init(elev=27, azim=-55)
    ax3.set_box_aspect((1.5, 1.35, 1))
    for axis in [ax3.xaxis, ax3.yaxis, ax3.zaxis]:
        axis.pane.fill=False
        axis.pane.set_edgecolor("0.92")
        axis._axinfo["grid"]["color"]=(.87, .87, .87, .6)
    ax3.text2D(.54, -.085, r"Equilibrium: $g_{+,G}=0$", transform=ax3.transAxes,
               ha="center", fontsize=9, color="0.35")
    fig.text(.5, .012, fr"$d={d},\quad \eta={eta},\quad M=14,\quad n=768$",
             ha="center", fontsize=9, color="0.35")
    save(fig, "preparation_memory_3d")


if __name__ == "__main__":
    collision_picture()
    weak_physical()
    weak_response()
    preparation_memory()
