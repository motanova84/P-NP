#!/usr/bin/env python3
"""
Inventory of incomplete lemmas in Lean files.
Analyzes sorry statements and categorizes them by context.
"""

import re
import os
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple

def find_lean_files(root_dir: str) -> List[Path]:
    """Find all .lean files in the directory."""
    return list(Path(root_dir).rglob("*.lean"))

def extract_sorries_with_context(filepath: Path) -> List[Dict]:
    """
    Extract sorry statements with surrounding context.
    
    Returns:
        List of dictionaries with line number, context, and type
    """
    sorries = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return sorries
    
    for i, line in enumerate(lines, 1):
        if 'sorry' in line.lower():
            # Get context (previous lines for theorem/lemma name)
            context_lines = []
            start = max(0, i - 5)
            for j in range(start, i):
                context_lines.append(lines[j].strip())
            
            # Try to identify what kind of sorry this is
            context_str = ' '.join(context_lines)
            
            sorry_type = 'unknown'
            if 'theorem' in context_str.lower():
                sorry_type = 'theorem'
            elif 'lemma' in context_str.lower():
                sorry_type = 'lemma'
            elif 'def' in context_str.lower():
                sorry_type = 'definition'
            elif 'example' in context_str.lower():
                sorry_type = 'example'
            elif ':=' in context_str or 'by' in context_str:
                sorry_type = 'proof'
            
            # Extract name if possible
            name_match = re.search(r'(theorem|lemma|def)\s+(\w+)', context_str)
            name = name_match.group(2) if name_match else 'unnamed'
            
            sorries.append({
                'line': i,
                'type': sorry_type,
                'name': name,
                'context': context_str[:200],  # First 200 chars
                'line_content': line.strip()
            })
    
    return sorries

def generate_report(root_dir: str) -> str:
    """Generate comprehensive report of all sorry statements."""
    
    lean_files = find_lean_files(root_dir)
    
    all_sorries = {}
    sorry_by_type = defaultdict(int)
    sorry_by_file = defaultdict(int)
    
    for filepath in lean_files:
        sorries = extract_sorries_with_context(filepath)
        if sorries:
            rel_path = filepath.relative_to(root_dir)
            all_sorries[str(rel_path)] = sorries
            sorry_by_file[str(rel_path)] = len(sorries)
            
            for sorry in sorries:
                sorry_by_type[sorry['type']] += 1
    
    # Generate report
    report = []
    report.append("=" * 80)
    report.append("LEAN PROOF INVENTORY - Sorry Statement Analysis")
    report.append("=" * 80)
    report.append("")
    
    # Summary statistics
    total_sorries = sum(sorry_by_file.values())
    report.append(f"Total sorry statements: {total_sorries}")
    report.append(f"Files with sorries: {len(all_sorries)}")
    report.append("")
    
    # By type
    report.append("By Type:")
    report.append("-" * 40)
    for sorry_type, count in sorted(sorry_by_type.items(), key=lambda x: -x[1]):
        report.append(f"  {sorry_type:20s}: {count:4d}")
    report.append("")
    
    # By file (top 10)
    report.append("Top 10 Files by Sorry Count:")
    report.append("-" * 40)
    for filepath, count in sorted(sorry_by_file.items(), key=lambda x: -x[1])[:10]:
        report.append(f"  {count:4d}  {filepath}")
    report.append("")
    
    # Detailed breakdown for high-priority files
    report.append("=" * 80)
    report.append("DETAILED BREAKDOWN - Critical Files")
    report.append("=" * 80)
    report.append("")
    
    # Focus on main theorem files
    priority_files = [
        'P_neq_NP.lean',
        'TseitinExpander.lean',
        'TreewidthToIC.lean',
        'InformationComplexity.lean',
        'FormalVerification.lean'
    ]
    
    for priority_file in priority_files:
        matching_files = [f for f in all_sorries.keys() if priority_file in f]
        for filepath in matching_files:
            sorries = all_sorries[filepath]
            report.append(f"\nFile: {filepath}")
            report.append(f"Sorry count: {len(sorries)}")
            report.append("-" * 40)
            
            # Group by type
            by_type = defaultdict(list)
            for sorry in sorries:
                by_type[sorry['type']].append(sorry)
            
            for sorry_type, items in by_type.items():
                report.append(f"\n  {sorry_type.upper()} ({len(items)} total):")
                for sorry in items[:5]:  # Show first 5 of each type
                    report.append(f"    Line {sorry['line']:4d}: {sorry['name']}")
                if len(items) > 5:
                    report.append(f"    ... and {len(items) - 5} more")
            report.append("")
    
    # Recommendations
    report.append("=" * 80)
    report.append("RECOMMENDATIONS")
    report.append("=" * 80)
    report.append("")
    report.append("Priority 1 - Critical Path:")
    report.append("  1. Complete P_neq_NP.lean main theorem")
    report.append("  2. Complete TseitinExpander.lean hard instance construction")
    report.append("  3. Complete TreewidthToIC.lean information complexity bounds")
    report.append("")
    report.append("Priority 2 - Supporting Lemmas:")
    report.append("  4. Complete InformationComplexity.lean framework")
    report.append("  5. Complete FormalVerification.lean end-to-end proof")
    report.append("")
    report.append("Estimated work:")
    if total_sorries < 50:
        effort = "LOW - Can be completed in focused session"
    elif total_sorries < 200:
        effort = "MEDIUM - Requires systematic approach over multiple sessions"
    else:
        effort = "HIGH - Substantial proof engineering required"
    report.append(f"  {effort}")
    report.append("")
    
    return '\n'.join(report)

def main():
    """Main entry point."""
    root_dir = "/home/runner/work/P-NP/P-NP"
    
    report = generate_report(root_dir)
    print(report)
    
    # Save to file
    output_file = "/tmp/lean_sorry_inventory.txt"
    with open(output_file, 'w') as f:
        f.write(report)
    print(f"\nReport saved to: {output_file}")

if __name__ == "__main__":
    main()
