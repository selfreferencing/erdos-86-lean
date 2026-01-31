# Research Assistant Setup Guide: Erdős 86 Conjecture Project
**Date:** January 31, 2026

---

## What This Project Is

You'll be working on the **Erdős 86 Conjecture**: proving that 2^86 is the last power of 2 with no zero digit in base 10.

**Current status:** OPEN PROBLEM (proof attempts from Jan 24 failed)

**Current approach:** Researching ML1 (Structured Shrinking-Target Property) to prove finiteness

---

## Setup Required in Your macOS Account

### 1. Install Claude Code CLI

```bash
# Install Claude Code
brew install anthropics/claude/claude-code

# Or download from https://claude.ai/download
```

### 2. Configure Claude API Key

You'll need an Anthropic API key (Kevin will provide this):

```bash
# Set up API key
claude auth login

# Or set environment variable
export ANTHROPIC_API_KEY="your-key-here"
```

Add to your `~/.zshrc` or `~/.bash_profile`:
```bash
export ANTHROPIC_API_KEY="your-key-here"
```

### 3. Install Python Dependencies

Python 3 should already be on macOS. Install NumPy:

```bash
pip3 install numpy
# Or
python3 -m pip install numpy
```

### 4. Install Git (if not already installed)

```bash
# Check if git is installed
git --version

# If not, install via Xcode Command Line Tools
xcode-select --install
```

### 5. Clone the Project Repository

```bash
# Navigate to where you want the project
cd ~/Desktop

# Clone the repository (URL will be provided)
git clone <repository-url> esc_stage8

# Navigate into it
cd esc_stage8
```

---

## Project Structure

```
esc_stage8/
├── STATUS_CHECKPOINT_2026_01_30.md    # Current status, what's been tried
├── ML1_RESEARCH_PLAN.md               # Your primary task
├── ML1_LITERATURE_FINDINGS.md         # Papers we found
├── M3_86_CONJECTURE_SESSION.md        # Deep analysis from Gemini
├── GPT_RESPONSE_SYNTHESIS.md          # All approaches tried (Parts I-XXII)
├── Zeroless/                          # Python experiments
│   ├── exp86_zeroless_only_transitions.py
│   ├── exp87_5adic_structure.py
│   ├── fourier_analysis_ZL.py         # Fourier decay analysis
│   └── ...
├── GPT_PROMPTS/                       # All prompts sent to GPT
│   ├── APPROACH54A_RESPONSE.md
│   ├── APPROACH55A_RESPONSE.md
│   └── ...
└── continued_fraction_theta.py        # CF analysis of log₁₀(2)
```

---

## How to Use Claude Code

### Start a session in your project:

```bash
cd ~/Desktop/esc_stage8
claude
```

### Key commands within Claude:

- `/help` - Get help
- `/resume` - Resume a previous session
- Read files: "Read STATUS_CHECKPOINT_2026_01_30.md"
- Run Python: "Run Zeroless/fourier_analysis_ZL.py"
- Search: "Search for 'shrinking target' in markdown files"

### Resume this specific session:

Once you clone the repo, you can say:
> "I'm Kevin's RA working on the Erdős 86 Conjecture. Read STATUS_CHECKPOINT_2026_01_30.md and ML1_RESEARCH_PLAN.md and summarize where we are."

---

## Your Primary Task: ML1 Research

**Goal:** Prove or find a path to proving the Structured Shrinking-Target Property (ML1)

**What we've done so far:**
1. ✅ Fourier analysis (no decay found - bad news)
2. ✅ Continued fraction analysis (θ not badly approximable)
3. ✅ Literature search (found promising 2025 "Hitting Times" paper)

**Next steps (from ML1_RESEARCH_PLAN.md):**

### Priority 1: Read "Hitting Times" Paper
- URL: https://arxiv.org/html/2510.07450
- Understand transversality proof
- Check if it extends to exponentially many intervals

### Priority 2: Algebraic Structure Analysis
- See ML1_RESEARCH_PLAN.md Direction 2
- S-arithmetic properties
- Shapira 2024 techniques

### Priority 3: Contact Experts
- Draft emails to:
  - Beresnevich, Datta, Ghosh, Ward (rectangular targets)
  - Shapira (algebraic structure)

---

## Key Background Files to Read (in order)

1. **STATUS_CHECKPOINT_2026_01_30.md** - Current state, what's been tried
2. **ML1_RESEARCH_PLAN.md** - Your task
3. **ML1_LITERATURE_FINDINGS.md** - Papers found
4. **M3_86_CONJECTURE_SESSION.md** - Deep analysis (optional, for context)

---

## Running Experiments

### Run existing experiments:

```bash
cd ~/Desktop/esc_stage8

# Fourier analysis
python3 Zeroless/fourier_analysis_ZL.py

# Continued fraction
python3 continued_fraction_theta.py

# Earlier experiments
python3 Zeroless/exp86_zeroless_only_transitions.py
```

### Create new experiments:

Save Python files in `Zeroless/` directory with naming:
- `expXX_description.py` (where XX is next number)

---

## Git Workflow

### Pull latest changes:
```bash
git pull origin main
```

### Save your work:
```bash
git add .
git commit -m "Description of what you did"
git push origin main
```

### Create a branch for major changes:
```bash
git checkout -b ra-ml1-analysis
# Do your work
git push origin ra-ml1-analysis
# Then create a pull request
```

---

## Communication

### With Kevin:
- Push changes to GitHub regularly
- Document findings in markdown files
- Use clear commit messages

### With Claude:
- Start sessions with: "Continue working on ML1 for Erdős 86"
- Reference files: "Read ML1_RESEARCH_PLAN.md"
- Ask for help: "Explain the transversality argument in the Hitting Times paper"

---

## Troubleshooting

### Claude Code not working:
```bash
# Check installation
claude --version

# Re-authenticate
claude auth login

# Check API key
echo $ANTHROPIC_API_KEY
```

### Python issues:
```bash
# Check Python version (need 3.x)
python3 --version

# Install NumPy if missing
pip3 install numpy
```

### Git issues:
```bash
# Configure git
git config --global user.name "Your Name"
git config --global user.email "your.email@example.com"
```

---

## Important Notes

1. **Don't modify STATUS_CHECKPOINT** - that's the canonical record
2. **Create new files** for your findings (e.g., `ML1_PROGRESS_Feb01.md`)
3. **Comment your Python code** clearly
4. **Save work frequently** - commit to git every hour or so
5. **Ask Claude for help** - it has full context on this project

---

## Quick Start Checklist

- [ ] Install Claude Code CLI
- [ ] Set up Anthropic API key
- [ ] Install NumPy
- [ ] Clone the repository
- [ ] Read STATUS_CHECKPOINT_2026_01_30.md
- [ ] Read ML1_RESEARCH_PLAN.md
- [ ] Run `python3 Zeroless/fourier_analysis_ZL.py` to verify setup
- [ ] Start Claude session: `claude`
- [ ] Ask Claude: "Continue ML1 research on Erdős 86"

---

## Questions?

If you get stuck:
1. Ask Claude for help (it knows this project)
2. Read the relevant markdown files
3. Check the experiments in `Zeroless/`
4. Contact Kevin

Good luck! This is a genuinely open problem - if we solve it, it's publishable!
