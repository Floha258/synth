import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from io import StringIO

# Data input as a multi-line string (since the data is small)
data = """Solver,abs,add,add_apollo,and,array,constant,false,identity,multiple_types,mux,npn4_1789,poly,precond,rand_dnf,rand_formula,true,xor,zero
cvc5,3.125s,13.090s,TO,1.020s,Error,0.537s,0.220s,0.179s,Error,3.180s,TO,98.271s,Error,258.886s,10.822s,0.179s,2.486s,TO
yices,2.215s,5.813s,11.408s,0.838s,Error,Error,0.210s,0.161s,Error,2.324s,15.264s,Error,Error,13.698s,5.979s,0.155s,1.643s,3.532s
z3,3.448s,8.577s,13.731s,1.516s,5.817s,0.761s,0.483s,0.245s,3.424s,3.659s,17.597s,5.794s,1.313s,22.607s,9.494s,0.211s,2.697s,6.218s"""

# Replace 'TO' with '1000s' directly in the data
data = data.replace('TO', '1000s')

# Read the data into a pandas DataFrame
df = pd.read_csv(StringIO(data), sep=',')

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
            annotation_y_position = 1e-2 * (2 + i * 1.0)  # Stagger annotations more significantly
            ax.text(index[j] + i * bar_width, annotation_y_position, f'Error\n{solver}', color='black', ha='center', va='center', fontsize=8)
        elif value == 1000:  # Timeout case (already replaced in the data)
            ax.bar(index[j] + i * bar_width, value, bar_width, color=timeout_color, label='Timeout' if i == 0 and j == 0 else "")
            annotation_y_position = value / (2 + i * 1.0)  # Stagger annotations more significantly
            ax.text(index[j] + i * bar_width, annotation_y_position, f'TO\n{solver}', color='black', ha='center', va='center', fontsize=8)
        else:  # Normal case
            ax.bar(index[j] + i * bar_width, value, bar_width, color=normal_colors[i], label=solver if j == 0 else "")

# Set the y axis to logarithmic scale
ax.set_yscale('log')

# Customize y-axis ticks for better readability with more crucial values
y_ticks = [0.01, 0.1, 1, 5, 10, 50, 100, 500, 1000]
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
plt.savefig('solver_performance_comparison_annotated.png')

# Show the plot
plt.show()
