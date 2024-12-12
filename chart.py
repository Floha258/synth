import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from io import StringIO

# Data input as a multi-line string (since the data is small)
data = """Solver;p01;p02;p03;p04;p05;p06;p07;p08;p09;p10;p11;p12;p13;p14;p15;p16;p17;p18;p19;p20;p21;p22;p23;p24
cvc5;2.149s;2.263s;1.776s;1.074s;1.176s;1.174s;2.669s;2.736s;3.391s;3.909s;4.182s;3.824s;117.035s;295.706s;TO;66.566s;178.341s;1.945s;TO;Error;TO;TO;TO;TO
yices;2.102s;1.768s;1.836s;0.939s;1.011s;0.945s;4.336s;2.411s;2.302s;5.027s;3.869s;4.068s;16.685s;8.836s;9.782s;6.803s;15.171s;1.808s;120.205s;Error;TO;TO;TO;TO
z3;1.989s;5.376s;2.668s;1.295s;1.449s;1.282s;3.216s;3.153s;3.398s;4.004s;4.285s;4.130s;15.191s;6.521s;11.262s;7.924s;5.563s;2.539s;37.169s;TO;5366.104s;TO;TO;TO"""

# Replace 'TO' with '1000s' directly in the data
data = data.replace('TO', '12000s')

# Read the data into a pandas DataFrame
df = pd.read_csv(StringIO(data), sep=';')

df = df.replace('Error', np.nan)

# Convert the time strings to numeric values (in seconds)
for col in df.columns[1:]:
    df[col] = df[col].str.replace('s', '').astype(float)

# Plotting
fig, ax = plt.subplots(figsize=(14, 8))

# Set positions and width for bars
bar_width = 0.25
index = np.arange(len(df.columns) - 1)

# Define colors: normal, timeout, error
normal_colors = ['skyblue', 'lightgreen', 'orange']  # Different colors for each solver
timeout_color = 'yellow'
error_color = 'red'

# Plot bars for each solver, annotating errors and timeouts
for i, solver in enumerate(df['Solver']):
    for j, value in enumerate(df.iloc[i, 1:]):
        if np.isnan(value):  # Error case
            ax.bar(index[j] + i * bar_width, 1e-2, bar_width, color=error_color, label='Error' if i == 0 and j == 0 else "")
            annotation_y_position = 1e-2 * (2 + i * 2.0)  # Stagger annotations more significantly
            ax.text(index[j] + i * bar_width, annotation_y_position, f'Error\n{solver}', color='black', ha='center', va='center', fontsize=8)
        elif value == 12000:  # Timeout case (already replaced in the data)
            ax.bar(index[j] + i * bar_width, value, bar_width, color=timeout_color, label='Timeout' if i == 0 and j == 0 else "")
            annotation_y_position = value / (2 + i * 3.0)  # Stagger annotations more significantly
            ax.text(index[j] + i * bar_width, annotation_y_position, f'TO\n{solver}', color='black', ha='center', va='center', fontsize=8)
        else:  # Normal case
            ax.bar(index[j] + i * bar_width, value, bar_width, color=normal_colors[i], label=solver if j == 0 else "")

# Set the y axis to logarithmic scale
ax.set_yscale('log')

# Customize y-axis ticks for better readability with more crucial values
y_ticks = [1, 5, 10, 50, 100, 500, 1000, 5000]
ax.set_yticks(y_ticks)
ax.get_yaxis().set_major_formatter(plt.ScalarFormatter())

# Add horizontal gridlines to make y-axis clearer
ax.grid(True, which="major", axis="y", linestyle="--", color="gray", alpha=0.7)

# Set labels
ax.set_xlabel('Test Cases')
ax.set_ylabel('Time (s)')
ax.set_title('Performance Comparison of Solvers')
ax.set_xticks(index + bar_width)
ax.set_xticklabels(df.columns[1:], rotation=45, ha='right')

# Add legend
ax.legend()

# Tight layout
plt.tight_layout()

# Save the plot to a file
plt.savefig('solver_performance_comparison_hack_annotated.pdf')

# Show the plot
plt.show()
